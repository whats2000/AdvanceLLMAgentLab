import Mathlib
import Aesop

-- Implementation
def minOfThree (a : Int) (b : Int) (c : Int) : Int :=
  -- << CODE START >>
  {{code}}
  -- << CODE END >>


-- Theorem: The returned value is the minimum of the three input numbers
def minOfThree_spec (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  -- << SPEC START >>
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)
  -- << SPEC END >>

theorem minOfThree_spec_satisfied (a : Int) (b : Int) (c : Int) :
  minOfThree_spec a b c (minOfThree a b c) := by
  -- << PROOF START >>
  unfold minOfThree minOfThree_spec
  {{proof}}
  -- << PROOF END >>
