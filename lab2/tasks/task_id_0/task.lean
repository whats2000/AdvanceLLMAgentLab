import Mathlib
import Aesop

-- Implementation
def ident (x : Nat) : Nat :=
  -- << CODE START >>
  {{code}}
  -- << CODE END >>


def ident_spec (x : Nat) (result: Nat) : Prop :=
  -- << SPEC START >>
  result = x
  -- << SPEC END >>

theorem ident_spec_satisfied (x : Nat) :
  ident_spec x (ident x) := by
  -- << PROOF START >>
  unfold ident ident_spec
  {{proof}}
  -- << PROOF END >>
