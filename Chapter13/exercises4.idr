
module Main

data Matter = Solid | Liquid | Gas

data MatterCmd : Type -> Matter -> Matter -> Type where
  Melt : MatterCmd () Solid Liquid
  Boil : MatterCmd () Liquid Gas
  Condense : MatterCmd () Gas Liquid
  Freeze : MatterCmd () Liquid Solid
  (>>=) : MatterCmd a x y -> (a -> MatterCmd b y z) -> MatterCmd b x z

iceSteam : MatterCmd () Solid Gas
iceSteam = do
  Melt
  Boil

steamIce : MatterCmd () Gas Solid
steamIce = do
  Condense
  Freeze
