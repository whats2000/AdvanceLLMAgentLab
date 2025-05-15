import json
import os
from typing import List

from src.parser import LeanGenerationTaskTemplate, Signature, TestCase


def generate_unit_tests(task_folder: str) -> str:
    """
    Generate Lean unit tests from a task folder containing signature.json and test.json files.
    
    Args:
        task_folder: Path to the task folder (e.g., "tasks/task_id_58")
        
    Returns:
        String containing the generated Lean test code
    """
    # Define file paths
    signature_path = os.path.join(task_folder, "signature.json")
    test_path = os.path.join(task_folder, "test.json")
    output_path = os.path.join(task_folder, "tests.lean")
    
    # Load the signature.json
    with open(signature_path, 'r') as f:
        signature_data = json.load(f)
        signature = Signature(**signature_data)
    
    # Load the test.json
    with open(test_path, 'r') as f:
        test_data = json.load(f)
        test_cases = [TestCase(**tc) for tc in test_data]
    
    # Create the template
    template = LeanGenerationTaskTemplate(signature)
    
    # Generate the unit tests
    test_code = []
    for test_case in test_cases:
        code_unit_test = template.render_code_unit_test(test_case)
        test_code.append(code_unit_test)
    
    # Join all tests with newlines
    result = "\n".join(test_code)
    
    # Write to file
    with open(output_path, 'w') as f:
        f.write(result)
    
    return result


def generate_tests_for_all_tasks(tasks_dir: str = "tasks") -> List[str]:
    """
    Find all task folders in the tasks directory.
    
    Args:
        tasks_dir: Path to the tasks directory
        
    Returns:
        List of paths to task folders that start with 'task_id_'
    """
    task_folders = []
    
    # Find all task directories
    for item in os.listdir(tasks_dir):
        if item.startswith("task_id_") and os.path.isdir(os.path.join(tasks_dir, item)):
            task_path = os.path.join(tasks_dir, item)
            task_folders.append(task_path)
    
    return task_folders


if __name__ == "__main__":
    # List all task folders
    task_folders = generate_tests_for_all_tasks()
    print(f"Found {len(task_folders)} task folders:")
    for folder in task_folders:
        print(f"  - {folder}")
    
    # Example: Generate tests for a specific task
    if task_folders:
        example_task = task_folders[0]
        print(f"\nGenerating tests for example task: {example_task}")
        generate_unit_tests(example_task)
        print(f"Tests generated and saved to {os.path.join(example_task, 'tests.lean')}")
    
    # Uncomment to generate tests for all tasks
    for folder in task_folders:
         try:
             generate_unit_tests(folder)
             print(f"Generated tests for {folder}")
         except Exception as e:
             print(f"Error generating tests for {folder}: {e}") 