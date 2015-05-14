module BrainFun.Interpreter

import System
import Debug.Error

import BrainFun.Commands
import BrainFun.State

%default total

total
init : String -> Program
init prog = case unpack prog of
              [] => EmptyProgram
              (c::cs) => Instructions [] c cs


mutual
  partial
  next : (Program -> Maybe Program) -> Program -> DataPtr -> IO ()
  next step prog ptr =
    case step prog of
      Nothing => return ()
      Just prog' => go prog' ptr

  partial
  go : Program -> DataPtr -> IO ()
  go EmptyProgram ptr = return ()
  go (Instructions left i right) ptr with (isCommand i)
    go (Instructions left i right) ptr   | Nothing    = next incrPC (Instructions left i right) ptr
    go (Instructions left '<' right) ptr | Just Left  = next incrPC (Instructions left '<' right) (moveLeft ptr)
    go (Instructions left '>' right) ptr | Just Right = next incrPC (Instructions left '>' right) (moveRight ptr)
    go (Instructions left '+' right) ptr | Just Incr  = next incrPC (Instructions left '+' right) (incr ptr)
    go (Instructions left '-' right) ptr | Just Decr  = next incrPC (Instructions left '-' right) (decr ptr)
    go (Instructions left '.' right) ptr | Just Out   =  do writeByte ptr
                                                          next incrPC (Instructions left '.' right) ptr
    go (Instructions left ',' right) ptr | Just In    =  next incrPC (Instructions left ',' right) !(readByte ptr)
    go (Instructions left '[' right) ptr | Just Begin =
      next (if get ptr == 0 then findEnd else incrPC) (Instructions left '[' right) ptr
    go (Instructions left ']' right) ptr | Just End   =
      next (if get ptr /= 0 then findBegin else incrPC) (Instructions left ']' right) ptr


namespace Main
  partial
  main : IO ()
  main = do prog <-
              case !getArgs of
                [] => init <$> getLine
                [prog] => init <$> getLine
                [prog, file] => init <$> readFile file
                args => error "Too many args."
            go prog initData
