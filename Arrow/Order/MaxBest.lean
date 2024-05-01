import Arrow.Order.Basic



namespace Arrow

open scoped Protorder



namespace Protorder
  variable {α : Type u}
    [self : Protorder α]


section max
  @[simp]
  abbrev is_max (a : α) : Prop :=
    ¬ ∃ (b : α), b < a

  /-- Set of `𝓜`ax elements of `α`. -/
  abbrev 𝓜 : Set α :=
    self.is_max

  theorem max_def : a ∈ 𝓜 ↔ ¬ ∃ (b : α), b < a :=
    by simp only [Membership.mem, Set.Mem]
  abbrev max_def' (a : α) := max_def (a := a)



  section fintype
    variable [Fintype α] [DecidableRel self.le]

    theorem is_max_iff_in_max : self.is_max a ↔ a ∈ 𝓜 :=
      by rfl
    theorem in_max_of_is_max : self.is_max a → a ∈ 𝓜 :=
      is_max_iff_in_max.mp
    theorem is_max_of_in_max : a ∈ 𝓜 → self.is_max a :=
      is_max_iff_in_max.mpr

    instance instDecidableIn𝓜 : Decidable (a ∈ self.𝓜) := by
      simp only [max_def]
      exact inferInstance

    def isMax (a : α) : Bool :=
      ∀ (b : α), ¬ b < a

    theorem isMax_iff_in_max : self.isMax a ↔ a ∈ 𝓜 :=
      by simp [isMax, max_def]

    theorem in_max_of_isMax : a ∈ 𝓜 → self.isMax a :=
      isMax_iff_in_max.mpr

    theorem isMax_of_in_max : self.isMax a → a ∈ 𝓜 :=
      isMax_iff_in_max.mp
  end fintype
end max



section best
  abbrev is_best (a : α) : Prop :=
    ∀ (b : α), a ≤ b

  /-- Set of best elements of `α`. -/
  abbrev 𝓒 : Set α :=
    is_best

  theorem best_def : a ∈ 𝓒 ↔ ∀ (b : α), a ≤ b := by
    simp [Membership.mem, Set.Mem]


  section fintype
    variable [Fintype α] [DecidableRel self.le]

    theorem best_cex_def : a ∈ 𝓒 ↔ ¬ ∃ (b : α), ¬ a ≤ b := by
      simp [not_exists]
      exact best_def
    theorem best_cex_def' (a : α) : a ∈ 𝓒 ↔ ¬ ∃ (b : α), ¬ a ≤ b :=
      best_cex_def

    theorem is_best_iff_in_best : self.is_best a ↔ a ∈ 𝓒 :=
      by rfl
    theorem in_best_of_is_best : self.is_best a → a ∈ 𝓒 :=
      is_best_iff_in_best.mp
    theorem is_best_of_in_best : a ∈ 𝓒 → self.is_best a :=
      is_best_iff_in_best.mpr

    instance instDecidableIn𝓒 [DecidableEqLE α] : Decidable (a ∈ self.𝓒) := by
      simp only [best_def]
      exact inferInstance

    def isBest (a : α) : Bool :=
      Decidable.decide (is_best a)

    theorem isBest_iff_in_best : self.isBest a ↔ a ∈ 𝓒 := by
      simp [isBest, Membership.mem, Set.Mem]

    theorem in_best_of_isBest : a ∈ 𝓒 → self.isBest a :=
      isBest_iff_in_best.mpr

    theorem isBest_of_in_best : self.isBest a → a ∈ 𝓒 :=
      isBest_iff_in_best.mp
  end fintype
end best



  theorem best_sub_max : self.𝓒 ⊆ self.𝓜
  | best, best_best => by
    rw [max_def]
    simp only [lt_def]
    intro ⟨cex, b_lt_cex⟩
    exact b_lt_cex.right $ best_best cex



section cex
  variable [Fintype α] [DecidableRel self.le]

  theorem not_max_iff_cex : a ∉ 𝓜 ↔ ∃ (b : α), b < a := by
    simp [max_def]
  theorem cex_of_not_max : a ∉ 𝓜 → ∃ (b : α), b < a :=
    not_max_iff_cex.mp
  theorem not_max_of_cex : (∃ (b : α), b < a) → a ∉ 𝓜 :=
    not_max_iff_cex.mpr

  theorem not_best_iff_cex : a ∉ 𝓒 ↔ ∃ (b : α), ¬ a ≤ b := by
    simp [best_def]
  theorem cex_of_not_best : a ∉ 𝓒 → ∃ (b : α), ¬ a ≤ b :=
    not_best_iff_cex.mp
  theorem not_best_of_cex : (∃ (b : α), ¬ a ≤ b) → a ∉ 𝓒 :=
    not_best_iff_cex.mpr
end cex


  instance instCoeOfPreorder : Coe (Preorder α) (Protorder α) where
    coe _ := Protorder.ofPreorder

end Protorder



export Protorder (
  𝓒 best_def
  𝓜 max_def
)



namespace _root_.Preorder
  theorem best_equiv
    [self : Preorder α]
    {b₁ b₂ : α} {h_b₁ : b₁ ∈ 𝓒} : b₂ ∈ 𝓒 ↔ b₁ ≈ b₂
  := by
    constructor
    · intro h_b₂
      rw [Protorder.equiv_def]
      exact ⟨h_b₁ b₂, h_b₂ b₁⟩
    · rw [Protorder.equiv_def, best_def]
      intro ⟨_, b₂_le_b₁⟩ a
      exact self.le_trans _ _ _ b₂_le_b₁ (h_b₁ a)
end _root_.Preorder



namespace QPreorder
  variable
    [self : QPreorder α]
    [F : Fintype α] [Inhabited α] [DecidableRel self.le]

  theorem exists_max_of (a : α) (h : a ∉ 𝓜) : ∃ (m : α), m < a ∧ m ∈ 𝓜 :=
    let ⟨b, b_lt_a⟩ := self.cex_of_not_max h
    if h : b ∈ 𝓜 then
      ⟨b, b_lt_a, h⟩
    else
      let ⟨m, m_lt_b, m_max⟩ :=
        have _decreasing_by :=
          wellFounded.wf.rank_lt_of_rel b_lt_a
        exists_max_of b h
      ⟨m, self.lt_trans m_lt_b b_lt_a, m_max⟩
  termination_by wellFounded.wf.rank a

  theorem exists_max : ∃ (m : α), m ∈ 𝓜 :=
    if h : default ∈ 𝓜 then ⟨default, h⟩ else
      let ⟨m, _, m_max⟩ := exists_max_of default h
      ⟨m, m_max⟩

  def maxFinset : Finset α :=
    F.elems.filter fun a => a ∈ 𝓜

  theorem maxFinset_nempty : Finset.Nonempty self.maxFinset := by
    simp [Finset.Nonempty, maxFinset]
    let ⟨m, m_max⟩ := self.exists_max
    exact ⟨m, F.complete m, m_max⟩

  def maxCexFinset (a : α) : Finset α :=
    F.elems.filter fun b => b < a

  theorem maxCexFinset_nempty (h : a ∉ 𝓜) : Finset.Nonempty (self.maxCexFinset a) := by
    simp [Finset.Nonempty, maxCexFinset]
    let ⟨m, m_lt_a, _⟩ := self.exists_max_of a h
    rw [self.lt_def] at m_lt_a
    exact ⟨m, F.complete m, m_lt_a⟩
end QPreorder
