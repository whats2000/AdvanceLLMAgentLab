from src.main import main_workflow, get_problem_and_code_from_taskpath, get_unit_tests_from_taskpath, get_task_lean_template_from_taskpath
from src.lean_runner import execute_lean_code
import re
import time

def test_all_tasks():
    task_folder_prefix = "tasks/"
    task_ids = [0, 58, 77, 127, 227, 404, 431, 433, 435, 441, 447]
    task_ids = [f"task_id_{task_id}" for task_id in task_ids]
    
    print(f"Starting test of {len(task_ids)} tasks: {', '.join(task_ids)}")
    testing_metadata = {}

    for task_id in task_ids:
        print(f"\n{'=' * 50}")
        print(f"Processing task {task_id}...")
        
        # Initializing the testing metadata for this task
        testing_metadata[task_id] = {
            "passes_unit_tests": False,
            "proof_is_correct": False,
            "runtime": 0.1
        }
        
        # Reading the problem description and the Lean code template
        print(f"Reading problem description and code template from {task_folder_prefix + task_id}...")
        problem_description, lean_code_template = get_problem_and_code_from_taskpath(task_folder_prefix + task_id)
        print(f"Problem description length: {len(problem_description)} characters")
        
        # Reading the unit tests
        print(f"Reading unit tests...")
        unit_tests = get_unit_tests_from_taskpath(task_folder_prefix + task_id)
        print(f"Unit tests length: {len(unit_tests)} characters")
                
        # Running the main workflow
        print(f"Running main workflow to generate solution...")
        start_time = time.time()
        generated_solution = main_workflow(problem_description, lean_code_template)
        end_time = time.time()
        runtime = end_time - start_time
        testing_metadata[task_id]["runtime"] = runtime
        print(f"Solution generated in {runtime:.2f} seconds")
        
        generated_code = generated_solution["code"]
        generated_proof = generated_solution["proof"]
        print(f"Generated code length: {len(generated_code)} characters")
        print(f"Generated proof length: {len(generated_proof)} characters")
        
        # Reading the task lean template, and putting the code and proof into the template.
        print(f"Loading Lean template and inserting generated solution...")
        task_lean_template_only_implementation = get_task_lean_template_from_taskpath(task_folder_prefix + task_id)
        task_lean_template_implementation_and_proof = get_task_lean_template_from_taskpath(task_folder_prefix + task_id)

        
        # Replacing the proof with a sorry for this template, only checking if the implementation is correct.
        task_lean_template_only_implementation = task_lean_template_only_implementation.replace("{{code}}", generated_code)
        task_lean_template_only_implementation = task_lean_template_only_implementation.replace("{{proof}}", "sorry")

        # Testing both the proof and the implementation
        task_lean_template_implementation_and_proof = task_lean_template_implementation_and_proof.replace("{{code}}", generated_code)
        task_lean_template_implementation_and_proof = task_lean_template_implementation_and_proof.replace("{{proof}}", generated_proof)
        
        
        # Executing the lean code
        print(f"Executing Lean code with implementation only (proof=sorry)...")
        lean_output_only_implementation = execute_lean_code(task_lean_template_only_implementation + f"\n\n{unit_tests}")
        print(f"Implementation test result: {'PASS' if 'executed successfully' in lean_output_only_implementation else 'FAIL'}")
        if "Lean Error" in lean_output_only_implementation:
            print(f"Implementation error: {lean_output_only_implementation.split('Lean Error:')[1].strip()[:150]}...")
        
        print(f"Executing Lean code with implementation and proof...")
        lean_output_implementation_and_proof = execute_lean_code(task_lean_template_implementation_and_proof + f"\n\n{unit_tests}")
        print(f"Full solution test result: {'PASS' if 'executed successfully' in lean_output_implementation_and_proof else 'FAIL'}")
        if "Lean Error" in lean_output_implementation_and_proof:
            print(f"Proof error: {lean_output_implementation_and_proof.split('Lean Error:')[1].strip()[:150]}...")
        
        # Update testing metadata based on results
        if "executed successfully" in lean_output_only_implementation and "sorry" not in generated_code:
            testing_metadata[task_id]["passes_unit_tests"] = True
            print("✅ Implementation passes unit tests")
        else:
            print("❌ Implementation fails unit tests")
            
        if "executed successfully" in lean_output_implementation_and_proof and "sorry" not in generated_proof:
            testing_metadata[task_id]["proof_is_correct"] = True
            print("✅ Proof is correct")
        else:
            print("❌ Proof has errors")
    
    # Printing summary of the testing results
    print(f"Testing Summary:")
    
    for task_id, metadata in testing_metadata.items():
        print(f"Task {task_id}:")
        print(f"  Passes Unit Tests: {metadata['passes_unit_tests']}")
        print(f"  Proof is Correct: {metadata['proof_is_correct']}")    
        print(f"  Runtime: {metadata['runtime']} seconds")
        print(f"---")
    
    return testing_metadata
        

if __name__ == "__main__":
    test_all_tasks()