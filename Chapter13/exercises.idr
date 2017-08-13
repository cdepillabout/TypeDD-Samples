
module Main

data DoorState = DoorClosed | DoorOpen

data DoorCmd : Type -> DoorState -> DoorState -> Type where
  Open : DoorCmd () DoorClosed DoorOpen
  Close : DoorCmd () DoorOpen DoorClosed
  RingBell : DoorCmd () state state

  Pure : ty -> DoorCmd ty a a
  (>>=) : DoorCmd a x y -> (a -> DoorCmd b y z) -> DoorCmd b x z

doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do
  RingBell
  Open
  RingBell
  Close
