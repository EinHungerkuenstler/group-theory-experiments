import Game.GroupTheoryGame.Group
import Game.GroupTheoryGame.Subgroup
import Game.GroupTheoryGame.Lattice
import Game.GroupTheoryGame.GaloisInsertion
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Init.Function

namespace GroupTheoryGame

structure Group_Hom (G H : Type _) [Group G] [Group H] :=
  to_fun : G → H
  map_mul' : ∀ x y : G, to_fun (x * y) = to_fun x * to_fun y


-- we give the identity homomorphism

variable {G : Type _} [Group G]

def Id_hom : Group_Hom G G := ⟨id,  fun _ _=> rfl⟩


-- we define the composition of homomorphisms

variable {G H K : Type _} [Group G] [Group H] [Group K]

def Comp_hom (f : Group_Hom G H) (g : Group_Hom H K) : Group_Hom G K :=
  ⟨fun x => g.to_fun (f.to_fun x) , fun _ _ => by simp [f.map_mul', g.map_mul']⟩

-- Group isomorphism as a bijection group homomorphism

structure Group_iso (G H : Type _) [Group G] [Group H] extends Group_Hom G H :=
  bijection : Function.Bijective to_fun


end GroupTheoryGame
