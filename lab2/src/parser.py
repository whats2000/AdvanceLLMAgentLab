from typing import Any, Dict, List, Optional

from pydantic import BaseModel, Field, Json
from rich import print


class Parameter(BaseModel):
    param_name: str = Field(description="The name of the parameter")
    param_type: str = Field(description="The type of the parameter")


class Signature(BaseModel):
    name: str = Field(description="The name of the function")
    parameters: List[Parameter] = Field(
        default_factory=list, description="The parameters of the function"
    )
    return_type: str = Field(description="The return type of the function")


class TestCase(BaseModel):
    input: Dict[str, Any] = Field(description="The input values for the test case")
    expected: Any = Field(description="The expected output for the test case")
    unexpected: List[Any] = Field(
        default_factory=list,
        description="The unexpected output values for the test case",
    )


class Specification(BaseModel):
    description: str = Field(
        description="The natural language description of the specification",
    )

    theorem: str = Field(
        description="The theorem that formally describes the specification with `sorry`",
    )

    proved_theorem: Optional[str] = Field(
        None,
        description="The proved theorem",
    )

    # TODO: Do we want examples for informal correctness guarantees?

    metadata: Optional[Json[Any]] = Field(None, description="The metadata")


class BenchmarkData(BaseModel):
    name: str = Field(
        description="The name of the benchmark data",
    )

    description: str = Field(
        description="The natural language description of the required program behavior",
    )

    signature: Signature = Field(
        description="The implementation function signature that defines the type of inputs and outputs",
    )

    specifications: List[Specification] = Field(
        description="A list of reference specifications that formally describe the desired program behavior based on the natural language description",
    )

    implementation: Optional[str] = Field(
        None,
        description="The reference implementation",
    )

    tests: List[TestCase] = Field(
        description="A list of test cases that cover the different possible behaviors of the implementation",
    )

    metadata: Optional[Json[Any]] = Field(None, description="The metadata")


class LeanGenerationTaskTemplate:
    def __init__(self, signature: Signature):
        self.signature = signature

    def render_header(self) -> str:
        return "import Plausible\n"

    def render_signature(self) -> str:
        rendered = f"def {self.signature.name}"
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" : {self.signature.return_type}"
        return rendered

    def render_code(self, code: str) -> str:
        rendered = self.render_signature()
        rendered += f" := {code}"
        return rendered

    def render_full_spec_name(self, *, spec_name: str) -> str:
        if spec_name == "":
            return f"{self.signature.name}_spec"
        return f"{self.signature.name}_spec_{spec_name}"

    def render_spec(self, spec: str, *, spec_name: str) -> str:
        full_spec_name = self.render_full_spec_name(spec_name=spec_name)
        rendered = f"@[reducible]\ndef {full_spec_name}"
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" (result: {self.signature.return_type}) : Prop := {spec}"
        return rendered

    def render_code_and_spec(self, code: str, spec: str, *, spec_name: str) -> str:
        rendered = self.render_code(code)
        rendered += "\n\n"
        rendered += self.render_spec(spec, spec_name=spec_name)
        return rendered

    def render_theorem_name(self, *, spec_name: str) -> str:
        return self.render_full_spec_name(spec_name=spec_name) + "_satisfied"

    def render_proof(
        self,
        proof: str,
        *,
        spec_name: str,
    ) -> str:
        rendered = f"theorem {self.render_theorem_name(spec_name=spec_name)}"
        for param in self.signature.parameters:
            rendered += f" ({param.param_name}: {param.param_type})"
        rendered += f" : {self.render_full_spec_name(spec_name=spec_name)}"
        for param in self.signature.parameters:
            rendered += f" {param.param_name}"
        rendered += f" ({self.signature.name}"
        for param in self.signature.parameters:
            rendered += f" ({param.param_name})"
        rendered += ")"
        rendered += f" := {proof}"
        return rendered

    @staticmethod
    def render_unit_test_value(lean_type: str, value: Any) -> str:
        if lean_type == "Bool":
            return str(value).lower()
        elif lean_type == "String":
            return f'"{value}"'
        else:
            return str(value)  # Use value as is for other types

    def render_code_unit_test(self, test_case: TestCase) -> str:
        rendered = f"#guard {self.signature.name}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += f" = ({self.render_unit_test_value(self.signature.return_type, test_case.expected)})"
        return rendered

    def render_spec_unit_test_correct_deciable(
        self, test_case: TestCase, *, spec_name: str
    ) -> str:
        rendered = f"#guard {self.render_full_spec_name(spec_name=spec_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += f" ({self.render_unit_test_value(self.signature.return_type, test_case.expected)})"
        return rendered

    def render_spec_unit_test_correct_undeciable(
        self, test_case: TestCase, *, spec_name: str
    ) -> str:
        rendered = f"example : {self.render_full_spec_name(spec_name=spec_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += f" ({self.render_unit_test_value(self.signature.return_type, test_case.expected)}) := by\n"
        rendered += f"  unfold {self.render_full_spec_name(spec_name=spec_name)}\n"
        rendered += "  plausible"
        return rendered

    def render_spec_unit_test_incorrect_deciable(
        self, test_case: TestCase, *, spec_name: str, unexpected_idx: int
    ) -> str:
        rendered = f"#guard ¬ ({self.render_full_spec_name(spec_name=spec_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += f" ({self.render_unit_test_value(self.signature.return_type, test_case.unexpected[unexpected_idx])})"
        rendered += ")"
        return rendered

    def render_spec_unit_test_incorrect_undeciable(
        self, test_case: TestCase, *, spec_name: str, unexpected_idx: int
    ) -> str:
        rendered = f"example : {self.render_full_spec_name(spec_name=spec_name)}"
        for param in self.signature.parameters:
            rendered += f" ({self.render_unit_test_value(param.param_type, test_case.input[param.param_name])})"
        rendered += f" ({self.render_unit_test_value(self.signature.return_type, test_case.unexpected[unexpected_idx])}) := by\n"
        rendered += f"  unfold {self.render_full_spec_name(spec_name=spec_name)}\n"
        rendered += "  plausible  -- should raise an error"
        return rendered


if __name__ == "__main__":
    signature = Signature(
        name="foo",
        parameters=[Parameter(param_name="x", param_type="Int")],
        return_type="Int",
    )
    template = LeanGenerationTaskTemplate(signature)
    code = "x + 1"
    spec = "result = x + 1"
    proof = "sorry"
    test_case = TestCase(input={"x": 1}, expected=2, unexpected=[3])

    rendered_code = template.render_code(code)
    rendered_spec = template.render_spec(spec, spec_name="add_one")
    rendered_proof = template.render_proof(proof, spec_name="add_one")
    rendered_code_unit_test = template.render_code_unit_test(test_case)
    rendered_spec_unit_test_correct_deciable = (
        template.render_spec_unit_test_correct_deciable(test_case, spec_name="add_one")
    )
    rendered_spec_unit_test_correct_undeciable = (
        template.render_spec_unit_test_correct_undeciable(
            test_case, spec_name="add_one"
        )
    )
    rendered_spec_unit_test_incorrect_deciable = (
        template.render_spec_unit_test_incorrect_deciable(
            test_case, spec_name="add_one", unexpected_idx=0
        )
    )
    rendered_spec_unit_test_incorrect_undeciable = (
        template.render_spec_unit_test_incorrect_undeciable(
            test_case, spec_name="add_one", unexpected_idx=0
        )
    )

    print(rendered_code)
    print(rendered_spec)
    print(rendered_proof)
    print(rendered_code_unit_test)
    print(rendered_spec_unit_test_correct_deciable)
    print(rendered_spec_unit_test_correct_undeciable)
    print(rendered_spec_unit_test_incorrect_deciable)
    print(rendered_spec_unit_test_incorrect_undeciable)