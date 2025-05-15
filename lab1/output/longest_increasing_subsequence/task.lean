import Std
open Std

def longestIncreasingSubsequence (nums : Array Int) : Int :=
  -- << CODE START >>
  Id.run do
    let n := nums.size
    if n == 0 then
      pure 0
    else
      -- dp[i] = length of LIS ending at i
      let mut dp := Array.replicate n 1
      -- Build dp
      for i in List.range n do
        for j in List.range i do
          if nums[j]! < nums[i]! then
            let newLen := dp[j]! + 1
            let oldLen := dp[i]!
            dp := dp.set! i (if newLen > oldLen then newLen else oldLen)
      -- Find the maximum in dp
      let mut ans := 0
      for i in List.range n do
        let v := dp[i]!
        ans := if v > ans then v else ans
      pure ans
  -- << CODE END >>

def longestIncreasingSubsequence_spec_isCorrect (nums : Array Int) (result : Int) : Prop :=
  -- << SPEC START >>
  if nums.isEmpty then
    -- empty ⇒ must return 0
    result = 0
  else
    -- non-empty ⇒ answer between 1 and nums.size
    1 ≤ result ∧ result ≤ nums.size ∧

    -- there is a strictly‐increasing subsequence of length = result
    ∃ (indices : List Nat),
      indices.length = result ∧
      -- all indices valid
      indices.all (· < nums.size) ∧
      -- strictly increasing sequence
      List.Pairwise (fun i j => i < j ∧ nums[i]! < nums[j]!) indices ∧

    -- no strictly longer valid subsequence exists
    ∀ (indices' : List Nat),
      indices'.length > result →
      ( indices'.any (· ≥ nums.size)
      ∨ ¬ List.Pairwise (fun i j => i < j ∧ nums[i]! < nums[j]!) indices' )
  -- << SPEC END >>

-- You can use the following to do unit tests, you don't need to submit the following code
/--
  A list of (input array, expected LIS length) test cases.
-/
def testCases : List (Array Int × Int) :=
  [ (#[10, 9, 2, 5, 3, 7, 101, 18], 4)
  , (#[0, 1, 0, 3, 2, 3], 4)
  , (#[7, 7, 7, 7, 7, 7, 7], 1)
  , (#[1], 1)
  , (#[1, 3, 6, 7, 9, 4, 10, 5, 6], 6)
  , (#[-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9], 12)
  , (#[10, 22, 9, 33, 21, 50, 41, 60, 80], 6)
  ]

#eval do
  for (nums, exp) in testCases do
    let res := longestIncreasingSubsequence nums
    if res == exp then
      IO.println s!"✔  nums={nums} ⇒ {res}"
    else
      IO.eprintln s!"✘  nums={nums} ⇒ got {res}, expected {exp}"
