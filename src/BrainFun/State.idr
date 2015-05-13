module BrainFun.State

%default total

||| A zipper over an infinite memory of bytes. The regions that have
||| been accessed are represented, while the unread/unwritten regions
||| are lists that are extended as necessary.
data DataPtr : Type where
  Focused : (left : List Bits8) -> (ptrVal : Bits8) -> (right : List Bits8) -> DataPtr

||| Debugging aid
dump : DataPtr -> String
dump (Focused l p r) = concatMap show (reverse l) ++ " -[" ++ show p ++ "]- " ++ concatMap show r

||| The initial state - an infinite sequence of zeroes.
initData : DataPtr
initData = Focused [] 0 []

||| Move the focus one place to the left
moveLeft : DataPtr -> DataPtr
moveLeft (Focused []        ptrVal right) = Focused []   0 (ptrVal :: right)
moveLeft (Focused (x::left) ptrVal right) = Focused left x (ptrVal :: right)

||| Move the focus one place to the right
moveRight : DataPtr -> DataPtr
moveRight (Focused left ptrVal [])         = Focused (ptrVal :: left) 0 []
moveRight (Focused left ptrVal (x::right)) = Focused (ptrVal :: left) x right

||| Modify the focused value
update : (Bits8 -> Bits8) -> DataPtr -> DataPtr
update f (Focused left ptrVal right) = Focused left (f ptrVal) right

||| Increment the focused value
incr : DataPtr -> DataPtr
incr = update (+1)

||| Decrement the focused value
decr : DataPtr -> DataPtr
decr = update (\x => x-1)

||| Set the focused value
set : Bits8 -> DataPtr -> DataPtr
set x = update (const x)

||| Get the focused value
get : DataPtr -> Bits8
get (Focused _ ptrVal _) = ptrVal

||| Read a byte of input and hackily convert it to Bits8
readByte : DataPtr -> IO DataPtr
readByte mem = do ch <- getChar
                  return $ set (prim__truncInt_B8 (cast ch)) mem

||| Write the current byte as a Char (yes, also a hack, but it makes it readable)
writeByte : DataPtr -> IO ()
writeByte mem = putChar (chr (prim__zextB8_Int (get mem)))
