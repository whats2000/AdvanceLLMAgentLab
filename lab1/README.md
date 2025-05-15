# Lean 4 Dataset Generator

This tool converts standard coding problems into Lean 4 dataset format with formal specifications.

## Overview

The script processes coding problems from the `input` folder and converts them into the required Lean 4 dataset format using the Gemini API. Each problem will generate 4 files:

1. `description.txt` - Detailed task description
2. `signature.json` - Function signature definition
3. `test.json` - Unit tests for the function
4. `task.lean` - Implementation and formal specification in Lean 4

## Requirements

- Python 3.8+
- Google Gemini API key
- Required Python packages: `google-genai`, `pydantic`

## Installation

```bash
pip install google-genai pydantic
```

## Usage

Set your Gemini API key as an environment variable (recommended):

```bash
# On Windows PowerShell
$env:GEMINI_API_KEY="your_api_key_here"

# Or pass it directly when running the script
python convert_to_lean.py --api-key YOUR_GEMINI_API_KEY
```

Options:
- `--input-dir`: Directory containing input coding problems (default: "input")
- `--output-dir`: Directory to save the generated Lean datasets (default: "output")
- `--api-key`: Google API key for Gemini (required if not set as environment variable)

## Input Format

Place your coding problems as markdown (.md) or text (.txt) files in the `input` folder. The script will process each file and create a corresponding folder in the `output` directory with the generated Lean 4 files.

## Output Structure

```
output/
  problem_name/
    description.txt
    signature.json
    test.json
    task.lean
```

## Example

Input file: `input/binary_search.md`

Will generate:
- `output/binary_search/description.txt`
- `output/binary_search/signature.json`
- `output/binary_search/test.json`
- `output/binary_search/task.lean`
