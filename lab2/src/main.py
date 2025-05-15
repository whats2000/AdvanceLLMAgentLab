import os
import argparse
from src.agents import Reasoning_Agent, LLM_Agent
from src.lean_runner import execute_lean_code
from typing import Dict, List, Tuple

type LeanCode = Dict[str, str]

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
    generated_function_implementation = "sorry"
    generated_proof = "sorry"

    # TODO Implement your coding workflow here. The unit tests will call this function as the main workflow.
    # Feel free to chain multiple agents together, use the RAG database (.pkl) file, corrective feedback, etc.
    # Please use the agents provided in the src/agents.py module, which include GPT-4o and the O3-mini models.
    ...

    # Example return for task_id_0
    generated_function_implementation = "x"
    generated_proof = "rfl"
    
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
    
    with open(os.path.join(task_path, "description.txt"), "r") as f:
        problem_description = f.read()

    with open(os.path.join(task_path, "task.lean"), "r") as f:
        lean_code_template = f.read()

    return problem_description, lean_code_template

def get_unit_tests_from_taskpath(task_path: str) -> List[str]:
    """
    Reads a directory in the format of task_id_*. It will read the file "tests.lean" and return the unit tests.
    """
    with open(os.path.join(task_path, "tests.lean"), "r") as f:
        unit_tests = f.read()
    
    return unit_tests

def get_task_lean_template_from_taskpath(task_path: str) -> str:
    """
    Reads a directory in the format of task_id_*. It will read the file "task.lean" and return the Lean code template.
    """
    with open(os.path.join(task_path, "task.lean"), "r") as f:
        task_lean_template = f.read()
    return task_lean_template