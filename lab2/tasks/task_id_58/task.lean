import Mathlib
import Aesop

-- Implementation
def hasOppositeSign (a : Int) (b : Int) : Bool :=
  -- << CODE START >>
  {{code}}
  -- << CODE END >>


-- Theorem: The result is true if a and b have opposite signs
def hasOppositeSign_spec (a : Int) (b : Int) (result: Bool) : Prop :=
  -- << SPEC START >>
  (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0) ↔ result
  -- << SPEC END >>

theorem hasOppositeSign_spec_satisfied (a : Int) (b : Int) :
  hasOppositeSign_spec a b (hasOppositeSign a b) := by
  -- << PROOF START >>
  unfold hasOppositeSign hasOppositeSign_spec
  {{proof}}
  -- << PROOF END >>
