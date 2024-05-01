import Mathlib



/-! # Additions to `Mathlib` types -/



/-! ## `Finset` -/

namespace Finset
  variable (self : Finset α)
end Finset

/-! ## `Fintype` -/

namespace Fintype
  variable [self : Fintype α]

  theorem elems_nempty [Inhabited α] : self.elems ≠ ∅ := by
    intro h_empty
    let absurd :=
      h_empty ▸ self.complete default
    contradiction

  theorem toList_elems_nempty [Inhabited α] : self.elems.toList ≠ [] := by
    intro toList_empty
    let elems_empty :=
      Finset.toList_eq_nil.mp toList_empty
    exact elems_nempty elems_empty
end Fintype



/-! ## `Finite` -/

namespace Finite
  variable [self : Finite α]


end Finite
