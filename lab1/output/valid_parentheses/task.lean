import Std
def isValidParentheses (s : String) : Bool :=
  -- << CODE START >>
  let rec loop : List Char → List Char → Bool
    | [],        stack    => stack.isEmpty
    | c :: cs,   stack    =>
      if c == '(' || c == '[' || c == '{' then
        -- opening bracket: push
        loop cs (c :: stack)
      else if c == ')' || c == ']' || c == '}' then
        -- closing bracket: must match top
        match stack with
        | top :: rest =>
          let ok := match top, c with
            | '(', ')' => true
            | '[', ']' => true
            | '{', '}' => true
            | _,    _  => false
          if ok then loop cs rest else false
        | []          => false
      else
        -- ignore other chars
        loop cs stack
  loop s.toList []
  -- << CODE END >>

def isValidParentheses_spec_isCorrect (s : String) (result : Bool) : Prop :=
  -- << SPEC START >>
  result =
    let rec well : List Char → List Char → Bool
      | [],      []    => true
      | [],      _     => false
      | c :: cs, st    =>
        if c == '(' then
          well cs ('(' :: st)
        else if c == ')' then
          match st with
          | '(' :: st' => well cs st'
          | _          => false
        else if c == '[' then
          well cs ('[' :: st)
        else if c == ']' then
          match st with
          | '[' :: st' => well cs st'
          | _          => false
        else if c == '{' then
          well cs ('{' :: st)
        else if c == '}' then
          match st with
          | '{' :: st' => well cs st'
          | _          => false
        else
          -- ignore any other character
          well cs st
    well s.toList []
  -- << SPEC END >>

-- You can use the following to do unit tests, you don't need to submit the following code
def testCases : List (String × Bool) :=
  [ ("()",           true)
  , ("()[]{}",       true)
  , ("(]",           false)
  , ("([)]",         false)
  , ("{[]}",         true)
  , ("",             true)
  , ("[",            false)
  , ("]",            false)
  , ("(((((((((((()))))))))))))",  false)
  , ("(((((((((((())))))))))))",   true)
  ]

#eval do
  for (s, exp) in testCases do
    let res := isValidParentheses s
    if res == exp then
      IO.println s!"✔  s={s} ⇒ {res}"
    else
      IO.eprintln s!"✘  s={s} ⇒ got {res}, expected {exp}"
