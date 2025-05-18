import os
import argparse
from src.agents import Reasoning_Agent, LLM_Agent
from src.lean_runner import execute_lean_code
from typing import Dict, List, Tuple

# Define the LeanCode type as a type alias
LeanCode = Dict[str, str]


def main_workflow(problem_description: str, task_lean_code: str = "") -> LeanCode:
    """
    Main workflow for the coding agent. This workflow takes in the problem description in natural language (description.txt) 
    and the corresponding Lean code template (task.lean). It returns the function implementation and the proof in Lean.
    
    Args:
        problem_description: Problem description in natural language. This file is read from "description.txt"
        task_lean_code: Lean code template. This file is read from "task.lean"
    
    Returns:
        LeanCode: Final generated solution, which is a dictionary with two keys: "code" and "proof".
    """
    import os
    import re
    from src.embedding_db import VectorDB
    from src.embedding_models import OpenAIEmbeddingModel, MiniEmbeddingModel
    import pickle

    # Initialize embedding model for RAG
    embedding_model = OpenAIEmbeddingModel()

    # Check if embeddings already exist, if not create them
    embedding_file = "database.npy"
    chunks_file = "database_chunks.pkl"

    # Create embeddings if they don't exist
    if not os.path.exists(embedding_file) or not os.path.exists(chunks_file):
        try:
            print(f"Creating embeddings database...")
            vector_db = VectorDB(directory="documents",
                                 vector_file=embedding_file,
                                 embedding_model=embedding_model)
            print(f"Embeddings database created successfully.")
        except Exception as e:
            print(f"Error creating embeddings: {e}")

    # Extract function signature, specifications, and patterns from task_lean_code
    function_name_match = re.search(r'def\s+(\w+)\s*\(', task_lean_code)
    function_name = function_name_match.group(1) if function_name_match else "unknown_function"

    function_signature_match = re.search(r'def\s+\w+\s*(\(.*?\)).*?:=', task_lean_code, re.DOTALL)
    function_signature = function_signature_match.group(1) if function_signature_match else "()"

    spec_match = re.search(r'-- << SPEC START >>(.*?)-- << SPEC END >>', task_lean_code, re.DOTALL)
    spec = spec_match.group(1).strip() if spec_match else ""

    # Initialize our agent system
    planning_agent = LLM_Agent(model="gpt-4o")
    generation_agent = LLM_Agent(model="gpt-4o")
    verification_agent = Reasoning_Agent(model="o3-mini")

    # -------------------- PLANNING PHASE --------------------
    print("Starting planning phase...")

    # Build planning prompt
    planning_prompt = [
        {"role": "system", "content":
            "You are an expert in Lean 4 theorem proving and programming. "
            "Your task is to analyze a programming problem and create a plan for implementing "
            "a solution in Lean 4 with formal proof. "
            "Break down the problem into clear steps that will guide the implementation."
         },
        {"role": "user", "content":
            f"I need to implement a function in Lean 4 with a formal proof. Here's the problem description:\n\n"
            f"{problem_description}\n\n"
            f"The function signature is: def {function_name}{function_signature}\n\n"
            f"The specification is:\n{spec}\n\n"
            f"Create a detailed plan for:\n"
            f"1. Implementing the function\n"
            f"2. Proving that the implementation satisfies the specification\n"
            f"Be specific about Lean 4 tactics and approaches that should be used."
         }
    ]

    # Get plan from planning agent
    plan = planning_agent.get_response(planning_prompt)
    print(f"Planning complete.")

    # -------------------- RAG LOOKUP PHASE --------------------
    print("Retrieving relevant examples from database...")

    # Build query for RAG
    rag_query = f"Lean 4 implementation and proof for {function_name} with specification {spec}"

    # Get relevant examples from RAG
    try:
        top_chunks, scores = VectorDB.get_top_k(embedding_file, embedding_model, rag_query, k=3)
        relevant_examples = "\n\n".join(top_chunks)
        print(f"Retrieved {len(top_chunks)} relevant examples.")
    except Exception as e:
        print(f"Error retrieving from RAG database: {e}")
        relevant_examples = "No relevant examples found."

    # -------------------- GENERATION PHASE --------------------
    print("Starting code and proof generation...")

    # Build generation prompt
    generation_prompt = [
        {"role": "system", "content":
            "You are an expert in Lean 4 theorem proving and programming. "
            "Your task is to implement a function in Lean 4 and provide a formal proof "
            "that it satisfies its specification. Be precise and follow Lean 4 syntax "
            "and proof techniques. Only return the implementation code and the proof, nothing else."
         },
        {"role": "user", "content":
            f"I need to implement a function in Lean 4 with a formal proof. Here's the problem description:\n\n"
            f"{problem_description}\n\n"
            f"The function signature is: def {function_name}{function_signature}\n\n"
            f"The specification is:\n{spec}\n\n"
            f"Here's the plan we'll follow:\n{plan}\n\n"
            f"Here are some relevant examples that might help:\n{relevant_examples}\n\n"
            f"Please provide ONLY the raw implementation code and proof with no labels, headers, or annotations:\n"
            f"1. The implementation code (without the def {function_name} part) - ONLY the right side of the := expression\n"
            f"2. The proof tactics (after the unfold line) - just the proof tactics\n\n"
            f"IMPORTANT: For the implementation, provide ONLY the right side of the := expression, not the full function definition.\n"
            f"For example, if the function is 'def add (a b : Nat) : Nat := a + b', only provide 'a + b'.\n"
            f"For the proof, provide the complete proof tactics that will work after the unfold statement, such as 'simp' or 'apply'.\n\n"
            f"Do NOT include any text like 'Corrected Code:', 'Implementation:', '---', or line dividers. "
            f"Do NOT include any nested function definitions. The code will be directly inserted into the Lean file."
         }
    ]

    # Get initial implementation and proof from generation agent
    generated_solution = generation_agent.get_response(generation_prompt)

    # Parse the generated solution to separate code and proof
    code_match = re.search(r'```lean\s*([\s\S]*?)```', generated_solution)
    if code_match:
        generated_solution = code_match.group(1)

    code_parts = re.split(r'(?i)proof:|theorem:', generated_solution)

    if len(code_parts) > 1:
        generated_function_implementation = code_parts[0].strip()
        generated_proof = code_parts[1].strip()
    else:
        # Try other patterns to separate code and proof
        code_proof_parts = re.split(r'-- Implementation|-- Proof', generated_solution)
        if len(code_proof_parts) > 1:
            generated_function_implementation = code_proof_parts[1].strip()
            generated_proof = code_proof_parts[2].strip() if len(code_proof_parts) > 2 else ""
        else:
            # As a last resort, assume the first half is code and second half is proof
            middle_point = len(generated_solution) // 2
            generated_function_implementation = generated_solution[:middle_point].strip()
            generated_proof = generated_solution[
                              middle_point:].strip()  # Clean up the code and proof - remove labels, headers, and markdown
        generated_function_implementation = re.sub(r'```.*?```', '', generated_function_implementation, flags=re.DOTALL)
        generated_proof = re.sub(r'```.*?```', '', generated_proof, flags=re.DOTALL)

        # Remove any additional formatting patterns that might appear
        for pattern in [r'(?i)implementation\s*:', r'(?i)code\s*:', r'(?i)corrected code\s*:', r'-{3,}', r'={3,}']:
            generated_function_implementation = re.sub(pattern, '', generated_function_implementation, flags=re.DOTALL)
            generated_proof = re.sub(pattern, '', generated_proof, flags=re.DOTALL)

        # Remove any proof headers that might appear
        for pattern in [r'(?i)proof\s*:', r'(?i)theorem\s*:']:
            generated_proof = re.sub(pattern, '', generated_proof, flags=re.DOTALL)

        # Remove duplicate function definitions if they appear
        if f"def {function_name}" in generated_function_implementation:
            generated_function_implementation = re.sub(
                rf'def\s+{function_name}\s*' + re.escape(function_signature) + r'\s*:=\s*', '',
                generated_function_implementation, flags=re.DOTALL)

        # Remove any 'unfold' statements from the proof
        generated_proof = re.sub(r'unfold.*?\n', '', generated_proof)

    # -------------------- VERIFICATION PHASE --------------------
    print("Starting verification and refinement...")

    # Build a test Lean code by substituting the generated code and proof into the template
    test_lean_code = task_lean_code.replace("{{code}}", generated_function_implementation)
    test_lean_code = test_lean_code.replace("{{proof}}", generated_proof)

    # Execute the Lean code to check for errors
    print("Executing initial solution...")
    execution_result = execute_lean_code(test_lean_code)
    print(f"Initial execution result: {'Success' if 'executed successfully' in execution_result else 'Error'}")
    if "Lean Error" in execution_result:
        print(f"Error details: {execution_result[:150]}...")

    # Check if there are errors and perform refinement if needed
    max_refinement_attempts = 3
    refinement_count = 0

    while "Lean Error" in execution_result and refinement_count < max_refinement_attempts:
        refinement_count += 1
        print(f"Refinement attempt {refinement_count}/{max_refinement_attempts}...")

        # Extract error message
        error_message = execution_result.split("Lean Error:")[
            1].strip() if "Lean Error:" in execution_result else execution_result

        # Build verification prompt for refinement
        verification_prompt = [
            {"role": "system",
             "content": "You are an expert in Lean 4 theorem proving and programming. "
                        "Your task is to fix errors in a Lean 4 implementation and proof. "
                        "Provide only the raw code and proof without any headers, labels or formatting."
             },
            {"role": "user", "content":
                f"I have a Lean 4 implementation and proof with errors. Here's the context:\n\n"
                f"Problem description: {problem_description}\n\n"
                f"Function signature: def {function_name}{function_signature}\n\n"
                f"Specification: {spec}\n\n"
                f"Current implementation:\n```lean\n{generated_function_implementation}\n```\n\n"
                f"Current proof:\n```lean\n{generated_proof}\n```\n\n"
                f"Error message:\n{error_message}\n\n"
                f"IMPORTANT: For the implementation, provide ONLY the right side of the := expression, not the full function definition.\n"
                f"For example, if the function is 'def add (a b : Nat) : Nat := a + b', only provide 'a + b'.\n"
                f"For the proof, provide the complete proof tactics that will work after the unfold statement.\n\n"
                f"Make sure the implementation and proof are syntactically valid Lean 4 code. DO NOT include 'def {function_name}' or extra keywords.\n"
                f"Please fix the implementation and/or proof to resolve these errors. "
                f"Return only the corrected code and proof without any extra text, labels, or formatting. "
                f"Do NOT include text like 'Corrected Code:', or dividers like '---'. "
                f"The output will be directly inserted into the Lean file."
             }
        ]

        # Get refinement from verification agent
        refinement_solution = verification_agent.get_response(verification_prompt)

        # Try to extract code and proof from the refinement solution
        code_match = re.search(r'```lean\s*([\s\S]*?)```', refinement_solution)
        if code_match:
            refinement_solution = code_match.group(1)

        code_parts = re.split(r'(?i)proof:|-- proof', refinement_solution)

        if len(code_parts) > 1:
            generated_function_implementation = code_parts[0].strip()
            generated_proof = code_parts[1].strip()
        else:
            # If we can't clearly separate, use the larger agent for a clearer separation
            clarification_prompt = [{"role": "system",
                                     "content": "You are an expert in Lean 4. Separate this solution into code and proof parts with NO labels, headers, or formatting markers."},
                                    {"role": "user",
                                     "content": f"Separate this Lean 4 solution into clear code and proof parts with no extra text:\n{refinement_solution}\n\nIMPORTANT: Do NOT include any text like 'Code:', 'Proof:', 'Corrected Code:', or line dividers like '---'. Just separate the actual code from the actual proof."}
                                    ]
            clarification = generation_agent.get_response(
                clarification_prompt)  # Try to parse the output more intelligently
            if "implementation" in clarification.lower() and "proof" in clarification.lower():
                # First check if there are clear headers we can use
                code_match = re.search(r'(?i)implementation[:\s]+(.*?)(?=proof[:\s]+|$)', clarification, re.DOTALL)
                proof_match = re.search(r'(?i)proof[:\s]+(.*)', clarification, re.DOTALL)

                if code_match and proof_match:
                    generated_function_implementation = code_match.group(1).strip()
                    generated_proof = proof_match.group(1).strip()
                else:
                    # Fallback to a simple split
                    parts = clarification.lower().split("proof", 1)
                    if len(parts) > 1:
                        generated_function_implementation = parts[0].strip()
                        generated_proof = parts[1].strip()
                    else:
                        # Last resort - try to find any implementation/proof indicators
                        for indicator in ["implementation", "def", "function", "code"]:
                            if indicator in clarification.lower():
                                parts = clarification.lower().split(indicator, 1)
                                if len(parts) > 1:
                                    potential_code = parts[1].strip()
                                    # Find where the proof might start
                                    for proof_indicator in ["proof", "theorem", "lemma"]:
                                        if proof_indicator in potential_code.lower():
                                            code_end = potential_code.lower().find(proof_indicator)
                                            if code_end > 0:
                                                generated_function_implementation = potential_code[:code_end].strip()
                                                generated_proof = potential_code[code_end:].strip()
                                                break

        # Clean up the code and proof
        generated_function_implementation = re.sub(r'```.*?```', '', generated_function_implementation, flags=re.DOTALL)
        generated_proof = re.sub(r'```.*?```', '', generated_proof, flags=re.DOTALL)

        # Remove any 'unfold' statements from the proof
        generated_proof = re.sub(r'unfold.*?\n', '', generated_proof)
        # Test the refined solution
        test_lean_code = task_lean_code.replace("{{code}}", generated_function_implementation)
        test_lean_code = test_lean_code.replace("{{proof}}", generated_proof)
        print(f"Executing refinement attempt {refinement_count}...")
        execution_result = execute_lean_code(test_lean_code)
        print(
            f"Refinement {refinement_count} result: {'Success' if 'executed successfully' in execution_result else 'Error'}")
        if "Lean Error" in execution_result:
            print(f"Error details: {execution_result[:150]}...")

        # If successful, break the loop
        if "executed successfully" in execution_result:
            print("Refinement successful!")
            break

        # Emergency fallback if we're not making progress
        if refinement_count == max_refinement_attempts - 1:
            print("Maximum refinement attempts reached. Trying a complete rewrite...")
            break
    # Final verification with both GPT-4o and o3-mini for robustness
    if "Lean Error" in execution_result:
        print("Using GPT-4o for final refinement...")

        # Simplify the prompt to avoid overwhelming the model
        final_verification_prompt = [
            {"role": "system",
             "content": "You are an expert in Lean 4 theorem proving and programming. "
                        "Your task is to rewrite a Lean 4 implementation and proof to fix errors. "
                        "Be minimal, precise, and focus on correctness. Provide only raw code and proof with no formatting."
             },
            {"role": "user", "content":
                f"Problem description: {problem_description[:300]}...\n\n"
                f"Function signature: def {function_name}{function_signature}\n\n"
                f"Specification: {spec}\n\n"
                f"Error message: {execution_result[:300] if len(execution_result) > 300 else execution_result}\n\n"
                f"IMPORTANT: For the implementation, provide ONLY the right side of the := expression, not the full function definition.\n"
                f"For example, if the function is 'def add (a b : Nat) : Nat := a + b', only provide 'a + b'.\n"
                f"For the proof, provide the complete proof tactics that will work after the unfold statement.\n\n"
                f"Make sure the implementation and proof are syntactically valid Lean 4 code. DO NOT include 'def {function_name}' or extra keywords.\n"
                f"Please provide a minimal working implementation and proof without any labels or formatting. "
                f"Do NOT include text like 'Implementation:', 'Proof:', headers, or dividers. "
                f"The code will be directly inserted into the Lean file."
             }
        ]

        # Get final refinement from GPT-4o
        print("Waiting for final refinement solution...")
        try:
            final_refinement = planning_agent.get_response(final_verification_prompt)
            print("Received final refinement solution.")
        except Exception as e:
            print(f"Error during final refinement: {e}")
            # Fallback to a very simple solution
            final_refinement = f"Implementation:\n{generated_function_implementation}\n\nProof:\n{generated_proof}"

        # Try to extract code and proof
        code_match = re.search(r'Implementation:[\s\n]*([\s\S]*?)(?:Proof:|$)', final_refinement, re.IGNORECASE)
        proof_match = re.search(r'Proof:[\s\n]*([\s\S]*)', final_refinement, re.IGNORECASE)

        if code_match:
            generated_function_implementation = code_match.group(1).strip()

        if proof_match:
            generated_proof = proof_match.group(1).strip()

        # Clean up the code and proof
        generated_function_implementation = re.sub(r'```.*?```', '', generated_function_implementation, flags=re.DOTALL)
        generated_proof = re.sub(r'```.*?```', '', generated_proof, flags=re.DOTALL)

        # Remove any 'unfold' statements from the proof
        generated_proof = re.sub(r'unfold.*?\n', '', generated_proof)

        # Final test
        test_lean_code = task_lean_code.replace("{{code}}", generated_function_implementation)
        test_lean_code = test_lean_code.replace("{{proof}}", generated_proof)
        print("Executing final solution...")
        try:
            final_execution_result = execute_lean_code(test_lean_code)
            print(
                f"Final execution result: {'Success' if 'executed successfully' in final_execution_result else 'Error'}")
            if "Lean Error" in final_execution_result:
                print(f"Final error details: {final_execution_result[:150]}...")
        except Exception as e:
            print(f"Error during final execution: {e}")
            final_execution_result = "Lean Error: Execution failed due to an unexpected error."
        if "executed successfully" in final_execution_result:
            print("Final refinement successful!")
        else:
            print("Warning: Final solution may still contain errors.")
            # Rely on the existing solution without hardcoded fallbacks
            print("Continuing with best generated solution.")

    # Return the final solution
    return {
        "code": generated_function_implementation,
        "proof": generated_proof
    }


def get_problem_and_code_from_taskpath(task_path: str) -> Tuple[str, str]:
    """
    Reads a directory in the format of task_id_*. It will read the file "task.lean" and also read the file 
    that contains the task description, which is "description.txt".

    After reading the files, it will return a tuple of the problem description and the Lean code template.

    Args:
        task_path: Path to the task file
    """
    problem_description = ""
    lean_code_template = ""

    with open(os.path.join(task_path, "description.txt"), "r", encoding="utf-8") as f:
        problem_description = f.read()

    # Read Lean code template
    with open(os.path.join(task_path, "task.lean"), "r", encoding="utf-8") as f:
        lean_code_template = f.read()

    return problem_description, lean_code_template


def get_unit_tests_from_taskpath(task_path: str) -> List[str]:
    """
    Reads a directory in the format of task_id_*. It will read the file "tests.lean" and return the unit tests.
    """
    with open(os.path.join(task_path, "tests.lean"), "r", encoding="utf-8") as f:
        unit_tests = f.read()

    return unit_tests


def get_task_lean_template_from_taskpath(task_path: str) -> str:
    """
    Reads a directory in the format of task_id_*. It will read the file "task.lean" and return the Lean code template.
    """
    with open(os.path.join(task_path, "task.lean"), "r", encoding="utf-8") as f:
        task_lean_template = f.read()
    return task_lean_template
