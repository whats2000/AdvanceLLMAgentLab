def binarySearch (array : List Int) (target : Int) : Int :=
  -- << CODE START >>
  def binarySearch (array : List Int) (target : Int) : Int :=
  -- Define a helper function for the recursive binary search.
  let rec binarySearchHelper (low : Int) (high : Int) : Int :=
    if low > high then
      -- Base case: target not found.
      -1
    else do
      -- Calculate the middle index.
      let mid : Int := low + (high - low) / 2
      -- Get the middle element.  Use `get!` because we know `mid` is within bounds
      let midVal : Int := array.get! mid

      -- Check if the middle element is the target.
      if midVal == target then
        -- Target found at the middle index.
        mid
      else if midVal < target then
        -- Target is in the right half of the array.
        binarySearchHelper (mid + 1) high
      else
        -- Target is in the left half of the array.
        binarySearchHelper low (mid - 1)

  -- Handle the case of an empty array.
  if array.isEmpty then
    -1
  else
    -- Start the binary search with the entire array.
    binarySearchHelper 0 (array.length - 1)
  -- << CODE END >>

def binarySearch_spec_isCorrect (array : List Int) (target : Int) (result : Int) : Prop :=
  -- << SPEC START >>
  def binarySearchSpec (array : List Int) (target : Int) (index : Int) : Prop :=
  if index = -1 then
    -- If the function returns -1, the target should not be in the array.
    ∀ i : Fin array.length, array.get i ≠ target
  else
    -- If the function returns a non-negative index, it must be a valid index
    -- and the element at that index must be equal to the target.
    0 ≤ index ∧ index < array.length ∧ array.get! index = target

-- Example usage (not part of the spec, but shows how to use it for verification):
-- #eval binarySearch [1, 2, 3, 4, 5] 3 -- Expected: 2
-- #eval binarySearch [1, 2, 3, 4, 5] 6 -- Expected: -1
-- #eval binarySearch [] 5          -- Expected: -1
  -- << SPEC END >>

-- You can use the following to do unit tests, you don't need to submit the following code
