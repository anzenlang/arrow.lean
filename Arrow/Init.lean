import Mathlib



/-! # Additions to `Mathlib` types -/



/-! ## `Fintype` -/

namespace Fintype
  variable [self : Fintype α]

  theorem elems_nempty [Inhabited α] : self.elems ≠ ∅ := by
    intro h_empty
    let absurd :=
      h_empty ▸ self.complete default
    contradiction
end Fintype



/-! ## `Finite` -/

namespace Finite
  variable [self : Finite α]


end Finite
