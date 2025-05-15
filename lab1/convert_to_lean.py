"""
Script to convert coding problems to Lean 4 dataset format.

This script processes coding problems from an input folder and
converts them into the required Lean 4 dataset format (4 files)
using the Gemini API.
"""

import argparse
import json
import logging
import os
import sys
from pathlib import Path
from typing import List, Dict, Any

from google import genai
from pydantic import BaseModel, Field

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Define Pydantic models for the Gemini API responses
class Parameter(BaseModel):
    param_name: str
    param_type: str

class FunctionSignature(BaseModel):
    name: str
    parameters: List[Parameter]
    return_type: str

class TestCase(BaseModel):
    input: Dict[str, Any]
    expected: Any
    unexpected: List[Any]

class LeanImplementation(BaseModel):
    code: str
    spec: str

class LeanDatapoint(BaseModel):
    description: str = Field(..., description="Description of the coding problem")
    signature: FunctionSignature = Field(..., description="Function signature in Lean")
    test_cases: List[TestCase] = Field(..., description="Test cases for the function")
    implementation: LeanImplementation = Field(..., description="Lean implementation and specification")

def create_directory(dir_path: Path) -> None:
    """Create directory if it doesn't exist."""
    if not dir_path.exists():
        dir_path.mkdir(parents=True)
        logger.info(f"Created directory: {dir_path}")

def read_problem(problem_path: Path) -> str:
    """Read problem description from file."""
    with open(problem_path, 'r', encoding='utf-8') as file:
        return file.read()

def generate_description(problem_text: str, client: genai.Client) -> str:
    """Generate description for the problem using Gemini API."""
    prompt = f"""
    Convert the following coding problem into a structured description for a Lean 4 implementation.
    
    PROBLEM:
    {problem_text}
    
    Format your response as follows:
    
    -----Description-----
    [Write a detailed task description of the program, explaining its functionality clearly]
    
    -----Input-----
    [Describe the input parameters in detail]
    
    -----Output-----
    [Describe the output and what the function should return]
    
    Make sure your description is clear, concise, and focuses on implementing this in Lean 4.
    """
    
    try:
        response = client.models.generate_content(
            model="gemini-2.0-flash",
            contents=prompt
        )
        return response.text
    except Exception as e:
        logger.error(f"Error generating description: {str(e)}")
        raise

def generate_signature(problem_text: str, description: str, client: genai.Client) -> FunctionSignature:
    """Generate function signature using Gemini API."""
    prompt = f"""
    You are a Lean 4 programming expert. Create a function signature in JSON format for the following problem:
    
    Problem Description:
    {description}
    
    Original Problem:
    {problem_text}
    
    Create a JSON signature that follows this exact format:
    {{
        "name": "functionName",
        "parameters": [
            {{
                "param_name": "parameterName", 
                "param_type": "ParameterType"
            }}
            // Additional parameters as needed
        ],
        "return_type": "ReturnType"
    }}
    
    Make sure to:
    1. Choose appropriate Lean 4 types (e.g., Int, Nat, String, List, Array, etc.)
    2. Use a clear, descriptive function name
    3. Properly name all parameters
    4. Format as valid JSON with no additional text
    """
    
    try:
        response = client.models.generate_content(
            model="gemini-2.0-flash",
            contents=prompt,
            config={
                "response_mime_type": "application/json",
                "response_schema": FunctionSignature,
            }
        )
        
        if hasattr(response, "parsed") and response.parsed:
            return response.parsed
        else:
            # Fallback to manual parsing if Pydantic validation fails
            logger.warning("Signature Pydantic validation failed, parsing manually")
            try:
                content = json.loads(response.text)
                return FunctionSignature(**content)
            except:
                # Try to extract JSON from the response if needed
                content = response.text
                import re
                json_match = re.search(r'(\{.*})', content, re.DOTALL)
                if json_match:
                    content = json_match.group(1)
                    content = json.loads(content)
                    return FunctionSignature(**content)
                raise
    except Exception as e:
        logger.error(f"Error generating signature: {str(e)}")
        raise

def generate_tests(problem_text: str, description: str, signature: FunctionSignature, client: genai.Client) -> List[TestCase]:
    """Generate test cases using Gemini API."""
    function_name = signature.name
    params = signature.parameters
    return_type = signature.return_type
    
    params_str = ", ".join([f"{p.param_name}: {p.param_type}" for p in params])
    
    prompt = f"""
    You are a Lean 4 programming expert. Create comprehensive unit tests for the following function:
    
    Function Name: {function_name}
    Parameters: {params_str}
    Return Type: {return_type}
    
    Problem Description:
    {description}
    
    Original Problem:
    {problem_text}
    
    Create at least 5 test cases in this exact JSON format with no additional text:
    [
        {{
            "input": {{ 
                // Input parameters as key-value pairs
            }},
            "expected": // Expected output value,
            "unexpected": [
                // Values that should NOT be returned
            ]
        }},
        // More test cases...
    ]
    
    Make sure to:
    1. Include at least 5 test cases
    2. Cover typical scenarios and edge cases
    3. Include at least one 'unexpected' value for each test
    4. Format as valid JSON with no additional text
    5. Use appropriate Lean 4 values based on the defined types
    """
    
    try:
        response = client.models.generate_content(
            model="gemini-2.0-flash",
            contents=prompt
        )
        
        # Extract JSON content from the response
        content = response.text
        import re
        json_match = re.search(r'(\[.*])', content, re.DOTALL)
        if json_match:
            content = json_match.group(1)
        
        test_cases = json.loads(content)
        return [TestCase(**tc) for tc in test_cases]
    except Exception as e:
        logger.error(f"Error generating tests: {str(e)}")
        raise

def generate_implementation(problem_text: str, description: str, signature: FunctionSignature, client: genai.Client) -> LeanImplementation:
    """Generate Lean implementation and specification using Gemini API."""
    function_name = signature.name
    params = signature.parameters
    return_type = signature.return_type
    
    # Format parameters in Lean style
    params_str = " ".join([f"({p.param_name} : {p.param_type})" for p in params])
    
    prompt = f"""
    You are a Lean 4 programming expert. Create a complete implementation and specification for the following function:
    
    Function Name: {function_name}
    Parameters: {params_str}
    Return Type: {return_type}
    
    Problem Description:
    {description}
    
    Original Problem:
    {problem_text}
    
    Create a Lean 4 implementation and specification. For the implementation, provide code that:
    1. Is correct and efficient
    2. Has at least 30 lines of code
    3. Includes clear comments explaining your logic
    4. Uses proper Lean 4 syntax and best practices
    
    For the specification, provide a formal property that:
    1. Fully constrains the program behavior
    2. Captures all essential properties and invariants
    3. Can be used to verify the correctness of the implementation
    
    Respond with a JSON object that contains:
    1. The code implementation (without the function signature)
    2. The specification (without the function signature)
    
    Format:
    {{
        "code": "your implementation code here",
        "spec": "your specification here"
    }}
    """
    
    try:
        response = client.models.generate_content(
            model="gemini-2.0-flash",
            contents=prompt,
            config={
                "response_mime_type": "application/json",
                "response_schema": LeanImplementation,
            }
        )
        
        if hasattr(response, "parsed") and response.parsed:
            return response.parsed
        else:
            # Fallback to manual parsing if Pydantic validation fails
            logger.warning("Implementation Pydantic validation failed, parsing manually")
            try:
                content = json.loads(response.text)
                return LeanImplementation(**content)
            except:
                # Try to extract JSON from the response if needed
                content = response.text
                import re
                json_match = re.search(r'(\{.*})', content, re.DOTALL)
                if json_match:
                    content = json_match.group(1)
                    content = json.loads(content)
                    return LeanImplementation(**content)
                raise
    except Exception as e:
        logger.error(f"Error generating implementation: {str(e)}")
        raise

def generate_lean_datapoint(problem_text: str, api_key: str) -> LeanDatapoint:
    """Generate Lean datapoint using Gemini API with separate calls for each component."""
    client = genai.Client(api_key=api_key)
    
    try:
        # Generate each component separately
        logger.info("Generating description...")
        description = generate_description(problem_text, client)
        
        logger.info("Generating function signature...")
        signature = generate_signature(problem_text, description, client)
        
        logger.info("Generating test cases...")
        test_cases = generate_tests(problem_text, description, signature, client)
        
        logger.info("Generating implementation and specification...")
        implementation = generate_implementation(problem_text, description, signature, client)
        
        return LeanDatapoint(
            description=description,
            signature=signature,
            test_cases=test_cases,
            implementation=implementation
        )
        
    except Exception as e:
        logger.error(f"Error generating complete Lean datapoint: {str(e)}")
        raise

def save_lean_datapoint(datapoint: LeanDatapoint, output_dir: Path) -> None:
    """Save the generated Lean datapoint to the output directory."""
    # Create output directory
    create_directory(output_dir)
    
    # Save description.txt
    # Use the description directly, if it's already formatted correctly
    if "-----Description-----" in datapoint.description:
        with open(output_dir / "description.txt", "w", encoding="utf-8") as f:
            f.write(datapoint.description)
    else:
        # Otherwise, format it as needed
        description_content = f"""-----Description----- 
{datapoint.description}

-----Input-----
The input consists of:
{", ".join([f"{param.param_name}: {param.param_type}" for param in datapoint.signature.parameters])}

-----Output-----
The output is a {datapoint.signature.return_type}
"""
        with open(output_dir / "description.txt", "w", encoding="utf-8") as f:
            f.write(description_content)
    
    # Save signature.json
    signature_json = {
        "name": datapoint.signature.name,
        "parameters": [
            {"param_name": param.param_name, "param_type": param.param_type}
            for param in datapoint.signature.parameters
        ],
        "return_type": datapoint.signature.return_type
    }
    with open(output_dir / "signature.json", "w", encoding="utf-8") as f:
        json.dump(signature_json, f, indent=2)
    
    # Save test.json
    # Convert Pydantic models to dictionaries
    test_cases_json = []
    for tc in datapoint.test_cases:
        test_cases_json.append({
            "input": tc.input,
            "expected": tc.expected,
            "unexpected": tc.unexpected
        })
    
    with open(output_dir / "test.json", "w", encoding="utf-8") as f:
        json.dump(test_cases_json, f, indent=2)
    
    # Save task.lean
    function_params = " ".join([f"({param.param_name} : {param.param_type})" for param in datapoint.signature.parameters])
    
    # Clean up code and spec if needed (remove unnecessary markers)
    code = datapoint.implementation.code
    spec = datapoint.implementation.spec
    
    # Clean up code markers if accidentally included
    code = code.replace("-- << CODE START >>", "").replace("-- << CODE END >>", "")
    spec = spec.replace("-- << SPEC START >>", "").replace("-- << SPEC END >>", "")
    
    # Format the Lean code
    task_lean_content = f"""def {datapoint.signature.name} {function_params} : {datapoint.signature.return_type} :=
  -- << CODE START >>
  {code}
  -- << CODE END >>

def {datapoint.signature.name}_spec_isCorrect {function_params} (result : {datapoint.signature.return_type}) : Prop :=
  -- << SPEC START >>
  {spec}
  -- << SPEC END >>

-- You can use the following to do unit tests, you don't need to submit the following code
"""
    with open(output_dir / "task.lean", "w", encoding="utf-8") as f:
        f.write(task_lean_content)
    
    logger.info(f"Saved Lean datapoint to {output_dir}")

def parse_args():
    """Parse command line arguments."""
    parser = argparse.ArgumentParser(description="Convert coding problems to Lean 4 dataset format")
    parser.add_argument("--input-dir", type=str, default="input",
                        help="Directory containing input coding problems")
    parser.add_argument("--output-dir", type=str, default="output",
                        help="Directory to save the generated Lean datasets")
    parser.add_argument("--api-key", type=str, default=None,
                        help="Google API key for Gemini (if not set in GEMINI_API_KEY env var)")
    return parser.parse_args()

def main():
    """Main function to process coding problems."""
    args = parse_args()
    
    # Get API key from command line argument or environment variable
    api_key = args.api_key or os.environ.get('GEMINI_API_KEY')
    
    if not api_key:
        logger.error("No API key provided. Set GEMINI_API_KEY environment variable or use --api-key")
        sys.exit(1)
    
    input_dir = Path(args.input_dir)
    output_dir = Path(args.output_dir)
    
    # Create output directory if it doesn't exist
    create_directory(output_dir)
    
    # Get list of problem files
    problem_files = list(input_dir.glob("*.txt"))
    if not problem_files:
        problem_files = list(input_dir.glob("*.md"))
    
    if not problem_files:
        logger.warning(f"No problem files found in {input_dir}")
        return
    
    logger.info(f"Found {len(problem_files)} problem files to process")
    
    # Process each problem
    for problem_file in problem_files:
        problem_name = problem_file.stem
        logger.info(f"Processing problem: {problem_name}")
        
        # Read problem
        problem_text = read_problem(problem_file)
        
        # Generate Lean datapoint
        try:
            datapoint = generate_lean_datapoint(problem_text, api_key)
            
            # Save datapoint
            problem_output_dir = output_dir / problem_name
            save_lean_datapoint(datapoint, problem_output_dir)
            
            logger.info(f"Successfully processed problem: {problem_name}")
        except Exception as e:
            logger.error(f"Error processing problem {problem_name}: {str(e)}")
    
    logger.info("Processing complete")

if __name__ == "__main__":
    main()
