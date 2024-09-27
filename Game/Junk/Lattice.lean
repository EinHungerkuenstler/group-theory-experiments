import Game.GroupTheoryGame.group
import Game.GroupTheoryGame.Subgroup
import Init.Prelude

namespace GroupTheoryGame

-- First, we define a preorder on a type α to be a relation ≤ that is reflexive and transitive.
class PartialOrder (α : Type _) extends LE α , LT α where
  left_refl : ∀ (a : α), a ≤ a
  left_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c
  left_iff_le : ∀ (a b : α), a ≤ b ↔ a < b ∨ a = b
  le_antisymm : ∀ (a b : α), a ≤ b → b ≤ a → a = b



-- We can then define a partial order to be a preorder that is also antisymmetric.



-- We define what a suprema is

class Sup (α : Type _) :=
  sup : α → α → α

-- We define what a infima is

class Inf (α : Type _) :=
  inf : α → α → α


--  We define what a semilattice sup is

class SemilatticeSup (α : Type _) extends PartialOrder α , Sup α where
  le_sup_left : ∀ (a b : α), a ≤ sup a b
  le_sup_right : ∀ (a b : α), b ≤ sup a b
  sup_le : ∀ (a b c : α), a ≤ c → b ≤ c → sup a b ≤ c

-- Now, we define what is a Lattice

class Lattice (α : Type _) extends SemilatticeSup α , Inf α where
  le_inf : ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ inf b c
  inf_le_left : ∀ (a b : α), inf a b ≤ a
  inf_le_right : ∀ (a b : α), inf a b ≤ b
  le_sup_inf : ∀ (a b c : α), a ≤ sup b c → inf a b ≤ c

end GroupTheoryGame
