import Mathlib
import Aesop

-- Implementation
def isDivisibleBy11 (n : Int) : Bool :=
  -- << CODE START >>
  {{code}}
  -- << CODE END >>


-- Theorem: The result is true if n is divisible by 11
def isDivisibleBy11_spec (n : Int) (result : Bool) : Prop :=
  -- << SPEC START >>
  n % 11 = 0 ↔ result
  -- << SPEC END >>

theorem isDivisibleBy11_spec_satisfied (n : Int) :
  isDivisibleBy11_spec n (isDivisibleBy11 n) := by
  -- << PROOF START >>
  unfold isDivisibleBy11 isDivisibleBy11_spec
  {{proof}}
  -- << PROOF END >>
