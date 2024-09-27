import Game.GroupTheoryGame.Group


namespace GroupTheoryGame

class Subgroup (α : Type _) [Group α] where
  carrier : Set α
  one_mem : 1 ∈ carrier
  mul_mem : ∀ {a b : α}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_mem : ∀ {a : α}, a ∈ carrier → a⁻¹ ∈ carrier

namespace Subgroup

variable {α : Type _}[Group α] (H : Subgroup α )

-- We define ∈ for subgroups

def mem (a : α) : Prop := a ∈ H.carrier

-- Two subgroups are equal if they have the same carrier

theorem two_subgroup_equal (H1 H2 : Subgroup α) (h : H1.carrier = H2.carrier) : H1 = H2 := by
  cases H1; cases H2
  simp [Subgroup.mk] at h
  simp [h]

-- Two subgroups are equal if and only if the subsets that be underlied by them are equal

theorem subgroup_equal_iff (H1 H2 : Subgroup α) : H1 = H2 ↔ H1.carrier = H2.carrier := by
  apply Iff.intro
  intro h
  simp [h]
  intro h
  exact two_subgroup_equal H1 H2 h

end Subgroup

end GroupTheoryGame
