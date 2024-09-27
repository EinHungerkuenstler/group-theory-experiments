import Mathlib.Tactic.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!

Basic definitions in group theory.

-/

-- We're overwriting inbuilt group theory here so we always work in
-- a namespace

namespace mygroup

-- definitions of the group classes

section groupdefs

-- definition of the group structure
class Group (G : Type _) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1
  mul_right_inv : ∀ a : G, a * a⁻¹ = 1

class CommGroup (G : Type _) extends Group G where
  mul_comm : ∀ a b : G, a * b = b * a

end groupdefs

/- Now we can work with the new `Group` structure and simplify proofs
   based on the updated axioms. -/

namespace group

open Group

variable {G : Type} [Group G]

-- We prove left_mul_cancel for group using `calc`.
lemma mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
  rw [← Group.one_mul b]
  rw [← Group.mul_left_inv a]
  rw [Group.mul_assoc]
  rw [h]
  rw [← Group.mul_assoc]
  rw [Group.mul_left_inv]
  rw [Group.one_mul]

lemma mul_eq_of_eq_inv_mul {a b c : G} (h : b = a⁻¹ * c) : a * b = c := by
  rw [h]
  rw [← Group.mul_assoc]
  rw [Group.mul_right_inv]
  rw [Group.one_mul]

-- We already proved `mul_eq_of_eq_inv_mul` but there are several other
-- similar-looking, but slightly different, versions of this. Here
-- is one.

lemma eq_mul_inv_of_mul_eq {a b c: G} (h : a * b = c) : a = c * b⁻¹ := by
  rw [← h]
  rw [Group.mul_assoc]
  rw [Group.mul_right_inv]
  rw [Group.mul_one]

lemma eq_inv_mul_of_mul_eq {a b c : G} (h : b * a = c) : a = b⁻¹ * c := by
  rw [← h]
  rw [← Group.mul_assoc]
  rw [Group.mul_left_inv]
  rw [Group.one_mul]

lemma mul_left_eq_self {a b : G} : a * b = b ↔ a = 1 := by
  constructor
  · intro h
    have h1 := eq_mul_inv_of_mul_eq h
    rw [Group.mul_right_inv] at h1
    exact h1
  · intro h
    rw [h]
    rw [Group.one_mul]

lemma mul_right_eq_self {a b : G} : a * b = a ↔ b = 1 := by
  constructor
  · intro h
    have h1 : b = a⁻¹ * a := by
      apply eq_inv_mul_of_mul_eq h
    rw [Group.mul_left_inv] at h1
    exact h1
  · intro h
    rw [h]
    rw [Group.mul_one]

-- Other useful lemmas

lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ := by
  rw [← Group.one_mul b⁻¹]
  apply eq_mul_inv_of_mul_eq h

lemma inv_inv (a : G) : a ⁻¹ ⁻¹ = a := by
  symm
  apply eq_inv_of_mul_eq_one
  exact Group.mul_right_inv a

lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  replace h := eq_mul_inv_of_mul_eq h
  rw [Group.one_mul] at h
  rw [h]
  rw [inv_inv]

lemma unique_id {e : G} (h : ∀ x : G, e * x = x) : e = 1 := by
  have h1 : e = e * 1 := by rw [Group.mul_one]
  rw [h1]
  apply h 1

-- Maybe add unique_id but with x * e = x

lemma unique_inv {a b : G} (h : a * b = 1) : b = a⁻¹ := by
  apply mul_left_cancel a
  rw [h, mul_right_inv a]

lemma mul_right_cancel (a b c : G) (h : b * a = c * a) : b = c := by
  calc b = b * 1 := by rw [Group.mul_one]
       _ = b * (a * a⁻¹) := by rw [Group.mul_right_inv]
       _ = b * a * a⁻¹ := by rw [Group.mul_assoc]
       _ = c * a * a⁻¹  := by rw [h]
       _ = c * (a * a⁻¹) := by rw [Group.mul_assoc]
       _ = c * 1 := by rw [Group.mul_right_inv]
       _ = c := by rw [Group.mul_one]

lemma mul_left_cancel_iff (a x y : G) : a * x = a * y ↔ x = y := by
  constructor
  · intro h
    apply mul_left_cancel a
    exact h
  · intro h
    rw [h]

lemma mul_right_cancel_iff (a x y : G) : x * a = y * a ↔ x = y := by
  constructor
  · intro h
    apply mul_right_cancel a
    exact h
  · intro h
    rw [h]

lemma inv_mul (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply mul_left_cancel (a * b)
  rw [Group.mul_right_inv]
  rw [Group.mul_assoc]
  rw [← Group.mul_assoc b]
  rw [Group.mul_right_inv]
  rw [Group.one_mul]
  rw [Group.mul_right_inv]

lemma one_inv : (1 : G)⁻¹ = 1 := by
  apply mul_left_cancel (1 : G)
  rw [Group.mul_right_inv]
  rw [Group.one_mul]

theorem inv_eq {a b : G}: a⁻¹ = b ↔ b⁻¹ = a := by
  constructor
  · rintro rfl
    rw [inv_inv]
  · intro h
    rw [← h]
    rw [inv_inv]

-- A commutative version using `CommGroup`.
theorem mul_comm {G : Type} [CommGroup G] (g h : G) : g * h = h * g :=
  CommGroup.mul_comm g h

end group

end mygroup
