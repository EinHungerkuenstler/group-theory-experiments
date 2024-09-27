import Mathlib.Tactic.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace Int

/-- The `n`-th iterate of an equivalence `f : X ≃ X`, where `n` is an integer.
For positive `n`, this is `f` composed with itself `n` times.
For negative `n`, this is the inverse of `f` composed `|n|` times. -/
def iterate {X : Type} (n : ℤ) (f : Equiv.Perm X) : Equiv.Perm X := f ^ n

namespace iterate

variable {X : Type} (m n : ℤ) (f : Equiv.Perm X) (x : X)

/-- Composition of iterates corresponds to addition of integers. -/
lemma comp : iterate m f (iterate n f x) = iterate (m + n) f x := by
  suffices : (f ^ m * f ^ n) x = (f ^ (m + n)) x
  exact this
  rw [zpow_add]

@[simp] lemma zero : iterate 0 f = Equiv.refl X := rfl

@[simp] lemma one : iterate 1 f = f := by
  ext x
  simp [iterate]

@[simp] lemma neg_one : iterate (-1) f = f.symm := by
  ext x
  simp [iterate]
  exact rfl

/-- Iterating `f` negatively corresponds to iterating its inverse. -/
lemma neg (a : ℤ) : iterate (-a) f = iterate a f.symm := by
  show f^(-a) = f⁻¹^a
  rw [zpow_neg]
  exact Eq.symm (inv_zpow f a)

lemma succ : iterate n f (f x) = iterate (n + 1) f x := comp n 1 f x

lemma succ' : f (iterate n f x) = iterate (n + 1) f x := by
  rw [add_comm]
  exact comp 1 n f x

/-- Iterating an iterate corresponds to multiplication of integers. -/
theorem mul (f : Equiv.Perm X) (a b : ℤ) : iterate a (iterate b f) = iterate (a * b) f := by
  rw [iterate, iterate, iterate]
  exact Eq.symm (zpow_mul' f a b)

end iterate

end Int
