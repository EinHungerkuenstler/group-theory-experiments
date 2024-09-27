import Mathlib.Tactic.Ring
import Game.GroupTheoryGame.Group.Basic
import Game.GroupTheoryGame.Int.Basic

namespace MyGroup

namespace Group

variable {G : Type _} [Group G]

open Int

/-- Left multiplication by `g` is a bijection. -/
def lmul (g : G) : G ≃ G where
  toFun := fun x ↦ g * x
  invFun := fun x ↦ g⁻¹ * x
  left_inv := by {
    intro x
    exact Eq.symm (eq_inv_mul_of_mul_eq rfl)
  }
  right_inv := by {
    intro x
    exact mul_eq_of_eq_inv_mul rfl
  }

/-- Define exponentiation in the group using integer iterations of `lmul g`. -/
def pow (g : G) (n : ℤ) : G := (Int.iterate n (lmul g)) 1

instance : Pow G ℤ where
  pow := pow

variable (n m : ℤ) (g h k : G)

lemma lmul_one : lmul g 1 = g := mul_one g

lemma lmul_symm : (lmul g).symm = lmul g⁻¹ := by
  ext x
  rfl

lemma lmul_symm' : (lmul g)⁻¹ = (lmul g).symm := rfl

lemma pow_def : g ^ n = (Int.iterate n (lmul g)) 1 := rfl

lemma pow_one_mul : (Int.iterate 1 (lmul g)) h = g * h := by
  rw [Int.iterate, zpow_one, lmul]; simp

@[simp] lemma pow_zero : g ^ (0 : ℤ) = 1 := by
  rfl

@[simp] lemma pow_one : g ^ (1 : ℤ) = g := by
  rw [pow_def, Int.iterate.one]
  exact mul_one g

theorem pow_neg : g ^ (-n) = (g⁻¹) ^ n := by
  rw [pow_def, pow_def, ← lmul_symm, ← iterate.neg, iterate.neg]

/-- A direct corollary. -/
@[simp] theorem pow_neg_one_inv (g : G) : g ^ (-1 : ℤ) = g⁻¹ := by
  rw [pow_neg, pow_one]

lemma iterate_succ : Int.iterate (n + 1) (lmul g) h = g * Int.iterate n (lmul g) h := by
  rw [add_comm, ← Int.iterate.comp, pow_one_mul]

lemma iterate_mul_assoc : (Int.iterate n (lmul g) h) * k = Int.iterate n (lmul g) (h * k) := by
  apply @Int.induction_on (fun z => (iterate z (lmul g)) h * k = (iterate z (lmul g)) (h * k)) n
  · simp
  · intro m ih
    rw [iterate_succ, mul_assoc, ih, ← iterate_succ]
  · intro m ih
    rw [show -(m : Int) - 1 = -((m : Int) + 1) by ring]
    rw [iterate.neg, lmul_symm, iterate_succ, mul_assoc,
        ← lmul_symm, ← iterate.neg, ih, lmul_symm,
        iterate_succ, ← lmul_symm, ← iterate.neg]

/-- Exponentiation and iteration are consistent with multiplication. -/
lemma pow_mul_eq_iterate (n : ℤ) : g ^ n * k = Int.iterate n (lmul g) k := by
  convert iterate_mul_assoc n g 1 k
  exact (one_mul k).symm

theorem pow_add : g ^ (m + n) = g ^ m * g ^ n := by
  rw [pow_def, pow_def, pow_def]
  rw [← iterate.comp, iterate_mul_assoc, one_mul]

theorem pow_sub : g ^ (m - n) = g ^ m * g ^ (-n) := by
  rw [sub_eq_add_neg, pow_add]

theorem pow_mul : g ^ (m * n) = (g ^ n) ^ m := by
  rw [pow_def, pow_def, pow_def]
  rw [← iterate.mul]
  congr; ext
  change (iterate n (lmul g)) x = ((iterate n (lmul g)) 1) * x
  rw [iterate_mul_assoc, one_mul]

theorem pow_inv : (g ^ n)⁻¹ = g⁻¹ ^ n := by
  apply @Int.induction_on (fun z => (g ^ z)⁻¹ = g⁻¹ ^ z) n
  · simp
    have h := (mul_left_eq_self (1 : G) (1 : G)⁻¹).mpr rfl
    rw [← h, mul_right_inv]
  · intros i hi
    rw [pow_add, pow_one, inv_mul, hi, add_comm, pow_add, pow_one]
  · intros i hi
    rw [pow_sub, sub_eq_add_neg, add_comm, pow_add, pow_neg, pow_neg, pow_one,
      inv_mul, inv_inv, ← pow_neg i, hi, pow_neg 1, inv_inv, pow_one]

@[simp] lemma one_pow : (1 : G) ^ n = 1 := by
  apply @Int.induction_on (fun z => (1 : G) ^ z = 1) n
  · exact pow_zero 1
  · intros i hi; rw [pow_add, hi, pow_one, one_mul]
  · intros i hi; rw [sub_eq_add_neg, pow_add, hi, one_mul, pow_neg, pow_one, one_inv]

theorem mul_pow {H : Type _} [CommGroup H] {g h : H} (n : ℤ) : (g * h) ^ n = g ^ n * h ^ n := by
  rw [pow_def, pow_def, pow_def, iterate_mul_assoc, one_mul]
  apply @Int.induction_on (fun z => (iterate z (lmul (g * h))) 1 = (iterate z (lmul g)) ((iterate z (lmul h)) 1)) n
  · simp
  · intros k hk
    rw [iterate_succ, iterate_succ, iterate_succ, hk, mul_assoc, mul_comm h,
        mul_comm h, ← iterate_mul_assoc]
  · intros k hk
    rw [show -(k : Int) - 1 = -((k : Int) + 1) by ring]
    rw [iterate.neg, iterate.neg, iterate.neg,
        lmul_symm, lmul_symm, lmul_symm,
        iterate_succ, iterate_succ, iterate_succ]
    rw [iterate.neg, iterate.neg, iterate.neg,
        lmul_symm, lmul_symm, lmul_symm] at hk
    rw [hk]
    rw [inv_mul, mul_comm h⁻¹, mul_assoc, mul_comm h⁻¹]
    rw [mul_comm h⁻¹, iterate_mul_assoc]

end Group

end MyGroup
