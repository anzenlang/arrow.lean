import Arrow.Order.Basic



namespace Arrow

open scoped Protorder



namespace Protorder
  variable {α : Type u}
    [self : Protorder α]


section max
  @[simp]
  abbrev is_max (a : α) : Prop :=
    ∀ (b : α), ¬ b < a

  /-- Set of `𝓜`ax elements of `α`. -/
  abbrev 𝓜 : Set α :=
    self.is_max

  theorem 𝓜_def : a ∈ 𝓜 ↔ ∀ (b : α), ¬ b < a :=
    by simp only [Membership.mem, Set.Mem]



  section fintype
    variable [Fintype α] [DecidableRel self.le]

    theorem 𝓜_cex_def : a ∈ 𝓜 ↔ ¬ ∃ (b : α), b < a := by
      rw [not_exists]
      exact 𝓜_def

    theorem is_max_iff_in_𝓜 : self.is_max a ↔ a ∈ 𝓜 :=
      by rfl
    theorem in_𝓜_of_is_max : self.is_max a → a ∈ 𝓜 :=
      is_max_iff_in_𝓜.mp
    theorem is_max_of_in_𝓜 : a ∈ 𝓜 → self.is_max a :=
      is_max_iff_in_𝓜.mpr

    instance instDecidableIn𝓜 : Decidable (a ∈ self.𝓜) := by
      simp only [𝓜_def]
      exact inferInstance

    def isMax (a : α) : Bool :=
      ∀ (b : α), ¬ b < a

    theorem isMax_iff_in_𝓜 : self.isMax a ↔ a ∈ 𝓜 :=
      by simp [isMax, 𝓜_def]

    theorem in_𝓜_of_isMax : a ∈ 𝓜 → self.isMax a :=
      isMax_iff_in_𝓜.mpr

    theorem isMax_of_in_𝓜 : self.isMax a → a ∈ 𝓜 :=
      isMax_iff_in_𝓜.mp
  end fintype
end max



section best
  abbrev is_best (a : α) : Prop :=
    ∀ (b : α), a ≤ b

  /-- Set of best elements of `α`. -/
  abbrev 𝓒 : Set α :=
    is_best

  theorem 𝓒_def : a ∈ 𝓒 ↔ ∀ (b : α), a ≤ b := by
    simp [Membership.mem, Set.Mem]


  section fintype
    variable [Fintype α] [DecidableRel self.le]

    theorem is_best_iff_in_𝓒 : self.is_best a ↔ a ∈ 𝓒 :=
      by rfl
    theorem in_𝓒_of_is_best : self.is_best a → a ∈ 𝓒 :=
      is_best_iff_in_𝓒.mp
    theorem is_best_of_in_𝓒 : a ∈ 𝓒 → self.is_best a :=
      is_best_iff_in_𝓒.mpr

    instance instDecidableIn𝓒 [DecidableEqLE α] : Decidable (a ∈ self.𝓒) := by
      simp only [𝓒_def]
      exact inferInstance

    def isBest (a : α) : Bool :=
      Decidable.decide (is_best a)

    theorem isBest_iff_in_𝓒 : self.isBest a ↔ a ∈ 𝓒 := by
      simp [isBest, Membership.mem, Set.Mem]

    theorem in_𝓒_of_isBest : a ∈ 𝓒 → self.isBest a :=
      isBest_iff_in_𝓒.mpr

    theorem isBest_of_in_𝓒 : self.isBest a → a ∈ 𝓒 :=
      isBest_iff_in_𝓒.mp
  end fintype
end best



  theorem 𝓒_sub_𝓜 : self.𝓒 ⊆ self.𝓜
  | best, 𝓒_best => by
    rw [𝓜_cex_def]
    simp only [lt_def]
    intro ⟨cex, b_lt_cex⟩
    exact b_lt_cex.right $ 𝓒_best cex

end Protorder
