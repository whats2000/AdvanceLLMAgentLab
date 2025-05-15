import Mathlib
import Aesop

-- Implementation
def hasCommonElement (a : Array Int) (b : Array Int) : Bool :=
  -- << CODE START >>
  {{code}}
  -- << CODE END >>


-- Theorem: If the method returns true, there exists at least one common element between the two arrays; If the method returns false, there are no common elements between the two arrays
def hasCommonElement_spec (a : Array Int) (b : Array Int) (result : Bool) : Prop :=
  -- << SPEC START >>
  (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔ result
  -- << SPEC END >>

theorem hasCommonElement_spec_satisfied (a : Array Int) (b : Array Int) :
  hasCommonElement_spec a b (hasCommonElement a b) := by
  -- << PROOF START >>
  unfold hasCommonElement hasCommonElement_spec
  {{proof}}
  -- << PROOF END >>
