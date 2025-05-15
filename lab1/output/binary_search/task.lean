def binarySearch (array : Array Int) (target : Int) : Int :=
  -- << CODE START >>
  def binarySearch (array : Array Int) (target : Int) : Int :=
  -- Define a recursive helper function to perform the binary search
  let rec binarySearchHelper (low : Int) (high : Int) : Int :=
    if low > high then
      -- Base case: target not found
      -1
    else
      -- Calculate the middle index
      let mid : Int := low + (high - low) / 2 -- to prevent overflow

      -- Get the element at the middle index. We need to use 'get!' because we have proved mid < array.size through the implicit proof from low and high.
      let midVal := array.get! mid.toNat

      -- Check if the middle element is the target
      if midVal == target then
        -- Target found, return the index
        mid
      else if target < midVal then
        -- Target is in the left half, recursively search the left half
        binarySearchHelper low (mid - 1)
      else
        -- Target is in the right half, recursively search the right half
        binarySearchHelper (mid + 1) high

  -- Handle the case of an empty array
  if array.isEmpty then
    -1
  else
    -- Start the binary search with the entire array
    binarySearchHelper 0 (array.size - 1)

  -- << CODE END >>

def binarySearch_spec_isCorrect (array : Array Int) (target : Int) (result : Int) : Prop :=
  -- << SPEC START >>
  /- Formal specification of the binarySearch function.

The function binarySearch (array : Array Int) (target : Int) : Int satisfies the following properties:

1.  If the array is empty, the function returns -1.
2.  If the target is present in the array, the function returns the index of the first occurrence of the target.
3.  If the target is not present in the array, the function returns -1.
4.  The input array 'array' must be sorted in ascending order for the function to work correctly. This is a precondition.
5.  The returned index, if not -1, must be within the bounds of the array (0 <= index < array.size).
6. For any returned index i != -1, array[i] == target.
7. For any index j < i, array[j] != target, where i is the index returned and i != -1.

Formally:

∀ (array : Array Int) (target : Int),
  (∀ i j, i < j → array[i] <= array[j]) →  -- array is sorted
  if array.isEmpty then
    binarySearch array target = -1
  else if target ∈ array then
    ∃ (i : Nat), (i < array.size) ∧ (array[i] == target) ∧ (binarySearch array target = i) ∧ (∀ (j : Nat), j < i → array[j] != target)
  else
    binarySearch array target = -1

Note: The expression `target ∈ array` is meant as mathematical notation and is not a valid Lean expression. It signifies that there exists an index i such that array[i] == target.  It is used here for clarity in the specification.
-/ 
  -- << SPEC END >>

-- You can use the following to do unit tests, you don't need to submit the following code
