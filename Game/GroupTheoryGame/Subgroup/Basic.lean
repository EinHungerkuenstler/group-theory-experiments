import Mathlib.Data.Fintype.Card
import Game.GroupTheoryGame.Group.Basic
import Game.GroupTheoryGame.Group.Powers

namespace MyGroup

open MyGroup.Group

/- subgroups (bundled) -/

/-- A subgroup of a group G is a subset containing 1
and closed under multiplication and inverse. -/

structure Subgroup (G : Type) [Group G] :=
  (carrier : Set G)
  (one_mem' : 1 ∈ carrier)
  (mul_mem' : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier)
  (inv_mem' : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier)

-- Defintion of normal subgroup (in a bundled form)

structure Normal (G : Type) [Group G] extends Subgroup G :=
  (conj_mem' : ∀ {g : G} {a : G}, a ∈ carrier → g * a * g⁻¹ ∈ carrier)

namespace Subgroup

variable {G : Type} [Group G] (H : Subgroup G)

-- Instead let's define ∈ directly
instance : Membership G (Subgroup G) := ⟨fun m H => m ∈ H.carrier⟩

/-- Two subgroups are equal if the underlying subsets are equal. -/
theorem ext' {H K : Subgroup G} (h : H.carrier = K.carrier) : H = K := by
  cases H
  cases K
  congr

@[ext]
theorem ext {H K : Subgroup G} (h : ∀ x : G, x ∈ H ↔ x ∈ K) : H = K := by
  apply ext'
  ext x
  exact h x

lemma mem_coe {g : G} {H : Subgroup G} : g ∈ H.carrier ↔ g ∈ H := by
  rfl

/-- Two subgroups are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {H K : Subgroup G} :
  H.carrier = K.carrier ↔ H = K := by
  constructor
  · intro hHc
    apply ext'
    exact hHc
  · intro hHK
    rw [hHK]

/-- A subgroup contains the group's 1. -/
theorem one_mem : (1 : G) ∈ H := H.one_mem'

/-- A subgroup is closed under multiplication. -/
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := Subgroup.mul_mem' H

/-- A subgroup is closed under inverse -/
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H := Subgroup.inv_mem' _

/-- A subgroup is closed under integer powers -/
theorem pow_mem {x : G} {n : ℤ} : x ∈ H → x ^ n ∈ H := by
  intro hx
  apply @Int.induction_on (fun n => x ^ n ∈ H) n
  · rw [Group.pow_zero]
    exact H.one_mem
  · intro i hi
    convert H.mul_mem hi hx
    rw [Group.pow_add, Group.pow_one]
  · intros i hi
    convert H.mul_mem hi (H.inv_mem hx)
    rw [← Group.pow_neg_one_inv, ← Group.pow_add ]; congr

@[simp] theorem inv_mem_iff {x :G} : x⁻¹ ∈ H ↔ x ∈ H := by
  constructor
  · intro hxH
    have h := H.inv_mem hxH
    rw [Group.inv_inv] at h
    exact h
  · intro hxH
    exact H.inv_mem hxH

instance : Coe (Subgroup G) (Set G) := ⟨Subgroup.carrier⟩

lemma mem_coe' {g : G} : g ∈ (H : Set G) ↔ g ∈ H := mem_coe

instance (K : Subgroup G) : Group (K : Set G) where
  mul := fun a b => ⟨a.1 * b.1, K.mul_mem' a.2 b.2⟩
  one := ⟨1, K.one_mem'⟩
  inv := fun a => ⟨a⁻¹, K.inv_mem' a.2⟩
  mul_assoc := fun a b c => by
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨c, hc⟩ := c
    apply Subtype.ext
    exact Group.mul_assoc a b c
  one_mul := fun a => by apply Subtype.ext; apply Group.one_mul
  mul_one := fun a => by apply Subtype.ext; apply Group.mul_one
  mul_left_inv := fun a => by apply Subtype.ext; apply Group.mul_left_inv
  mul_right_inv := fun a => by apply Subtype.ext; apply Group.mul_right_inv

/-- Returns index of a subgroup in a group -/
def index [Fintype G] (H : Subgroup G) [h : DecidablePred H.carrier] : ℕ :=
  have h' : Fintype H.carrier := by exact @setFintype _ _ H.carrier h;
  Fintype.card G / Fintype.card H.carrier

def index' [Fintype G] (H : Subgroup G) [h₁ : DecidablePred H.carrier] (J : Subgroup G) [h₂ : DecidablePred J.carrier] : ℕ :=
  have h₁' : Fintype H.carrier := by exact @setFintype _ _ H.carrier h₁;
  have h₂' : Fintype J.carrier := by exact @setFintype _ _ J.carrier h₂;
  Fintype.card H.carrier / Fintype.card J.carrier


end Subgroup

end MyGroup
