# Define variables
PYTHON := python3
LEAN := lean
SRC_DIR := src
TEST_DIR := tests

# Running the tests function.
.PHONY: test
test:
	@$(PYTHON) -m $(TEST_DIR).tests

# Zip everything in the current directory into submission.zip
.PHONY: zip
zip:
	@echo "📦 Creating submission.zip..."
	@which zip >/dev/null 2>&1 || (echo "⚡ Installing zip..."; sudo apt update && sudo apt install -y zip)
	@zip -r submission.zip . -x "submission.zip" ".git/*" "__pycache__/*"

# Help menu
.PHONY: help
help:
	@echo "🚀 Makefile Commands:"
	@echo "  make run-python    - Run Python script to execute Lean file"
	@echo "  make zip           - Create a zip file (submission.zip) of the entire project"
	@echo "  make install       - Install required dependencies (Python, Lean)"
	@echo "  make clean         - Remove compiled Lean files"
