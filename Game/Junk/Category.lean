import Mathlib.CategoryTheory.Category.Basic

namespace GroupTheoryGame

class Category (obj : Type _) :=
  Hom : obj → obj → Type _
  id : ∀ X : obj, Hom X X
  comp : ∀ {X Y Z : obj}, Hom X Y → Hom Y Z → Hom X Z
  id_comp : ∀ {X Y : obj} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : obj} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {W X Y Z : obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z), comp (comp f g) h = comp f (comp g h)

end GroupTheoryGame
