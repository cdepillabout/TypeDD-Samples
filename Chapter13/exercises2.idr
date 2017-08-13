
module Main

%default total

data Input = COIN | VEND | CHANGE | REFILL Nat

VendState : Type
VendState = (Nat, Nat)

data MachineCmd : Type -> VendState -> VendState -> Type where
  InsertCoin : MachineCmd () (pounds, chocs) (S pounds, chocs)
  Vend : MachineCmd () (S pounds, S chocs) (pounds, chocs)
  GetCoins : MachineCmd () (pounds, chocs) (Z, chocs)
  Refill : (bars : Nat) -> MachineCmd () (Z, chocs) (Z, bars + chocs)

  Display : String -> MachineCmd () state state
  GetInput : MachineCmd (Maybe Input) state state

  Pure : ty -> MachineCmd ty a a
  (>>=) : MachineCmd a x y -> (a -> MachineCmd b y z) -> MachineCmd b x z

data MachineIO : VendState -> Type where
  Do : MachineCmd a x y -> (a -> Inf (MachineIO y)) -> MachineIO x

namespace MachineDo
  (>>=) : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1
  (>>=) = Do

mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = Z} {chocs = _} = do
    Display "not enough money"
    machineLoop
  vend {pounds = _} {chocs = Z} = do
    Display "not enough chocolate"
    machineLoop
  vend {pounds = (S k)} {chocs = (S j)} = do
    Vend
    machineLoop

  refill : (bars : Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} bars = do
    Refill bars
    machineLoop
  refill {pounds = (S k)} _ = do
    Display "Can't refill with money in machine."
    machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop = do
    Just x <- GetInput
      | Nothing => do
          Display "Invalid input"
          machineLoop
    case x of
      COIN => do
        InsertCoin
        machineLoop
      VEND => vend
      CHANGE => do
        GetCoins
        Display "Change returned"
        machineLoop
      (REFILL num) => refill num
