def mergeSort (array : List Int) : List Int :=
  -- << CODE START >>
  def merge (left : List Int) (right : List Int) : List Int :=
  match left, right with
  | [], [] => [] -- Both lists are empty, return an empty list.
  | [], r => r    -- Left list is empty, return the right list.
  | l, [] => l    -- Right list is empty, return the left list.
  | lHead :: lTail, rHead :: rTail =>
    if lHead <= rHead then
      -- The head of the left list is smaller or equal, so prepend it to the result of merging the tail of the left list with the right list.
      lHead :: (merge lTail right)
    else
      -- The head of the right list is smaller, so prepend it to the result of merging the left list with the tail of the right list.
      rHead :: (merge left rTail)

-- Implementing Merge Sort

def mergeSort (array : List Int) : List Int :=
  -- Base case: If the list has 0 or 1 elements, it is already sorted.
  if array.length <= 1 then
    array
  else
    -- Divide the list into two halves.
    let mid := array.length / 2
    let left := array.take mid
    let right := array.drop mid

    -- Recursively sort the two halves.
    let sortedLeft := mergeSort left
    let sortedRight := mergeSort right

    -- Merge the sorted halves.
    merge sortedLeft sortedRight

-- Example Usage (for testing - outside the function definition)
#eval mergeSort [5, 2, 4, 7, 1, 3, 2, 6]
#eval mergeSort [3, 1, 2]
#eval mergeSort [1]
#eval mergeSort []

  -- << CODE END >>

def mergeSort_spec_isCorrect (array : List Int) (result : List Int) : Prop :=
  -- << SPEC START >>
  def isSorted (list : List Int) : Bool :=
  match list with
  | [] => true
  | [_] => true
  | h1 :: h2 :: t =>
    if h1 <= h2 then
      isSorted (h2 :: t)
    else
      false

/-- Specification for mergeSort function. -/
/--
For any list `array`:
1. The output of `mergeSort array` is a sorted list.
2. The output of `mergeSort array` contains the same elements as `array`.
--/


theorem mergeSortSpec (array : List Int) : 
  (isSorted (mergeSort array)) -- Output is sorted
  ∧ (List.length (mergeSort array) = List.length array) -- Output has the same length as the input
  ∧ (forall x, x ∈ (mergeSort array) ↔ x ∈ array) -- Output has the same elements as the input
  :=
  sorry

  -- << SPEC END >>

-- You can use the following to do unit tests, you don't need to submit the following code
