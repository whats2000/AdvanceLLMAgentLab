import Mathlib
import Aesop

-- Implementation
def isGreater (n : Int) (a : Array Int) : Bool :=
  -- << CODE START >>
  {{code}}
  -- << CODE END >>


-- Theorem: If the result is true, then n is greater than all elements in the array; If the result is false, then there exists at least one element in the array that is greater than or equal to n
def isGreater_spec (n : Int) (a : Array Int) (result : Bool) : Prop :=
  -- << SPEC START >>
  (∀ i, i < a.size → n > a[i]!) ↔ result
  -- << SPEC END >>

theorem isGreater_spec_satisfied (n : Int) (a : Array Int) :
  isGreater_spec n a (isGreater n a) := by
  -- << PROOF START >>
  unfold isGreater isGreater_spec
  {{proof}}
  -- << PROOF END >>
