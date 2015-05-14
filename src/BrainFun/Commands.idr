module BrainFun.Commands

%default total

||| Programs are zippers into finite lists of characters
data Program : Type where
  EmptyProgram : Program
  Instructions : List Char -> Char -> List Char -> Program 

||| There are eight instructions. The type represents the actual
||| source character, which allows the datatype to be used as a view
||| over actual input characters.
data Instruction : Char -> Type where
  Left  : Instruction '<'
  Right : Instruction '>'
  Incr  : Instruction '+'
  Decr  : Instruction '-'
  Out   : Instruction '.'
  In    : Instruction ','
  Begin : Instruction '['
  End   : Instruction ']'

||| View a character as a command.
isCommand : (c : Char) -> Maybe (Instruction c)
isCommand '<' = Just Left
isCommand '>' = Just Right
isCommand '+' = Just Incr
isCommand '-' = Just Decr
isCommand '.' = Just Out
isCommand ',' = Just In
isCommand '[' = Just Begin
isCommand ']' = Just End
isCommand _ = Nothing

||| All valid instructions are recognized as they should be by isCommand.
||| That is, there's no spurious Nothings.
allCharsOk : (instr : Instruction c) -> isCommand c = Just instr
allCharsOk Left = Refl
allCharsOk Right = Refl
allCharsOk Incr = Refl
allCharsOk Decr = Refl
allCharsOk Out  = Refl
allCharsOk In = Refl
allCharsOk Begin = Refl
allCharsOk End = Refl

||| Increment the program counter. This operation is partial because
||| we may be at the end of the program.
incrPC : Program -> Maybe Program
incrPC EmptyProgram = Nothing
incrPC (Instructions left here []) = Nothing
incrPC (Instructions left here (x::xs)) = Just (Instructions (here :: left) x xs)

||| Find the matching '[', given the components of a non-empty program
||| zipper. Partial because we might run out of program.
findBegin : Program -> Maybe Program
findBegin EmptyProgram = Nothing
findBegin (Instructions l h r) = findBegin' l h r Z
  where findBegin' : List Char -> Char -> List Char -> Nat -> Maybe Program
        findBegin' [] _ _ _ = Nothing
        findBegin' ('['::left) here right Z = Just (Instructions ('['::left) here right)
        findBegin' ('['::left) here right (S n) = findBegin' left '[' (here::right) n
        findBegin' (']'::left) here right n = findBegin' left ']' (here::right) (S n)
        findBegin' (i::left) here right n = findBegin' left i (here::right) n



||| Find the matching '], given the components of a non-empty program
||| zipper. Partial because we might fall off the right of the program.
findEnd : Program -> Maybe Program
findEnd EmptyProgram = Nothing
findEnd (Instructions l h r) = findEnd' l h r Z
  where findEnd' : List Char -> Char -> List Char -> Nat -> Maybe Program
        findEnd' _ _ [] _ = Nothing
        findEnd' left here (']'::[]) _ = Nothing
        findEnd' left here (']'::next::right) Z = Just (Instructions (']'::here::left) next right)
        findEnd' left here (']'::next::right) (S n) = findEnd' (here::left) ']' (next::right) n
        findEnd' left here ('['::right) n = findEnd' (here::left) '[' right (S n)
        findEnd' left here (i::right) n = findEnd' (here::left) i right n
