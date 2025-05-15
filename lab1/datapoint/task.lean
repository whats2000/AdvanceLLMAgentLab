def minOfThree (a : Int) (b : Int) (c : Int) : Int :=
  -- << CODE START >>
  if a <= b && a <= c then a
  else if b <= a && b <= c then b
  else c
  -- << CODE END >>

def minOfThree_spec_isMin (a : Int) (b : Int) (c : Int) (result : Int) : Prop :=
  -- << SPEC START >>
  (result <= a ∧ result <= b ∧ result <= c) ∧ (result = a ∨ result = b ∨ result = c)
  -- << SPEC END >>

-- You can use the following to do unit tests, you don't need to submit the following code

#guard minOfThree 1 2 3 = 1
