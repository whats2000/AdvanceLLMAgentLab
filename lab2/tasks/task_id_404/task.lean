import Mathlib
import Aesop

-- Implementation
def myMin (a : Int) (b : Int) : Int :=
  -- << CODE START >>
  {{code}}
  -- << CODE END >>


-- Theorem: The minValue is either a or b; The minValue is less than or equal to both a and b
def myMin_spec (a : Int) (b : Int) (result : Int) : Prop :=
  -- << SPEC START >>
  (result ≤ a ∧ result ≤ b) ∧
  (result = a ∨ result = b)
  -- << SPEC END >>

theorem myMin_spec_satisfied (a : Int) (b : Int) :
  myMin_spec a b (myMin a b) := by
  -- << PROOF START >>
  unfold myMin myMin_spec
  {{proof}}
  -- << PROOF END >>
