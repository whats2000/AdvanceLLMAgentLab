import Mathlib
import Aesop

-- Implementation
def cubeElements (a : Array Int) : Array Int :=
  -- << CODE START >>
  {{code}}
  -- << CODE END >>


-- Theorem: The length of the output array must be the same as the length of the input array; Each element in the output array is the cube of the corresponding element in the input array
def cubeElements_spec (a : Array Int) (result : Array Int) : Prop :=
  -- << SPEC START >>
  (result.size = a.size) ∧
  (∀ i, i < a.size → result[i]! = a[i]! * a[i]! * a[i]!)
  -- << SPEC END >>

theorem cubeElements_spec_satisfied (a : Array Int) :
  cubeElements_spec a (cubeElements a) := by
  -- << PROOF START >>
  unfold cubeElements cubeElements_spec
  {{proof}}
  -- << PROOF END >>
