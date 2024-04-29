import Arrow.Init



namespace Arrow



class DecidableEqLE (α : Type u) extends LE α where
  toDecidableEq : DecidableEq α
  toDecidableLE : DecidableRel le

namespace DecidableEqLE
  variable [self : DecidableEqLE α]

  instance instDecidableEq : DecidableEq α :=
    self.toDecidableEq
  instance instDecidableLE : DecidableRel self.le :=
    self.toDecidableLE
end DecidableEqLE



class Protorder (α : Type u) extends LE α, LT α where
  lt_def' : ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬ b ≤ a

namespace Protorder
  variable [self : Protorder α]

section LT

  @[simp]
  theorem lt_def : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
    intros
    exact self.lt_def' _ _

  theorem lt_intro {a b : α} : a ≤ b → ¬ b ≤ a → a < b := by
    rw [self.lt_def]
    exact And.intro

  theorem lt_elim {a b : α} : a < b → a ≤ b ∧ ¬ b ≤ a := by
    rw [self.lt_def]
    exact id

  scoped instance instDecidableLT [DecidableRel self.le] : DecidableRel self.lt := by
    intro a b
    rw [self.lt_def]
    if h : a ≤ b then
      if h' : b ≤ a then
        simp [h']
        exact isFalse .elim
      else
        exact isTrue ⟨h, h'⟩
    else
      simp [h]
      exact isFalse .elim

  abbrev toDecidableLT [DecidableRel self.le] : DecidableRel self.toLT.lt :=
    self.instDecidableLT

  theorem lt_asymm : ∀ {a b : α}, a < b → ¬ b < a := by
    simp ; intros ; assumption

  scoped instance instIsAsymmLT : IsAsymm α self.lt where
    asymm _ _ := self.lt_asymm

  theorem lt_trans [T : IsTrans α LE.le] : ∀ {a b c : α}, a < b → b < c → a < c := by
    simp
    intro a b c ab nba bc _ncb
    apply And.intro (Trans.trans ab bc)
    intro ca
    apply nba
    exact T.trans _ _ _ bc ca

  scoped instance instIsTransLT [IsTrans α LE.le] : IsTrans α self.lt where
    trans _ _ _ := self.lt_trans

  theorem lt_irrefl : ∀ {a : α}, ¬ a < a := by
    simp

  scoped instance instIsIrreflLT : IsIrrefl α self.lt where
    irrefl _ := self.lt_irrefl

end LT



section Equiv

  abbrev equiv (a b : α) : Prop :=
     a ≤ b ∧ b ≤ a

  scoped instance instHasEquiv : HasEquiv α where
    Equiv := self.equiv

  theorem equiv_def : ∀ {a b : α}, a ≈ b ↔ a ≤ b ∧ b ≤ a := by
    simp [HasEquiv.Equiv]

  theorem equiv_intro {a b : α} : a ≤ b → b ≤ a → a ≈ b :=
    And.intro

  theorem equiv_elim {a b : α} : a ≈ b → a ≤ b ∧ b ≤ a := by
    rw [equiv_def]
    exact id

  theorem equiv_refl [R : IsRefl α LE.le] : ∀ {a : α}, a ≈ a := by
    simp [HasEquiv.Equiv]
    exact R.refl _

  scoped instance instIsReflEquiv [IsRefl α LE.le] : IsRefl α HasEquiv.Equiv where
    refl _ := self.equiv_refl

  theorem equiv_trans [T : IsTrans α LE.le] : ∀ {a b c : α}, a ≈ b → b ≈ c → a ≈ c := by
    simp [HasEquiv.Equiv, equiv]
    intro a b c ab ba bc cb
    exact And.intro
      (Trans.trans ab bc)
      (Trans.trans cb ba)

  scoped instance instIsTransEquiv [IsTrans α LE.le] : IsTrans α HasEquiv.Equiv where
    trans _ _ _ := self.equiv_trans

  theorem equiv_symm : ∀ {a b  : α}, a ≈ b → b ≈ a := by
    simp [HasEquiv.Equiv, equiv]
    intro a b ab ba
    exact ⟨ba, ab⟩

  scoped instance instIsSymmEquiv : IsSymm α HasEquiv.Equiv where
    symm _ _ := self.equiv_symm
end Equiv





  theorem le_of_not_gt [T : IsTotal α self.le] : ∀ {a b : α}, ¬ a > b → a ≤ b := by
    intro a b
    simp
    cases T.total a b
    <;> simp [*]

  theorem le_of_not_lt_inv [IsTotal α self.le] : ∀ {a b : α}, ¬ b < a → a ≤ b :=
    le_of_not_gt

end Protorder



open scoped Protorder



class IsLTTrans (α : Type u)
extends Protorder α, IsTrans α LT.lt

namespace IsLTTrans
  variable [self : IsLTTrans α]

  theorem lt_trans : ∀ {a b c : α}, a < b → b < c → a < c :=
    self.toIsTrans.trans _ _ _
end IsLTTrans



class IsLTEquivLTTrans (α : Type u)
extends Protorder α, @Trans α α α LT.lt HasEquiv.Equiv LT.lt

namespace IsLTEquivLTTrans
  variable [self : IsLTEquivLTTrans α]

  theorem trans_lt_equiv_lt : ∀ {a b c : α}, a < b → b ≈ c → a < c :=
    trans
end IsLTEquivLTTrans



class IsEquivLTLTTrans (α : Type u)
extends Protorder α, @Trans α α α HasEquiv.Equiv LT.lt LT.lt

namespace IsEquivLTLTTrans
  variable [self : IsEquivLTLTTrans α]

  theorem trans_equiv_lt_lt : ∀ {a b c : α}, a ≈ b → b < c → a < c :=
    trans
end IsEquivLTLTTrans



class IsEquivTrans (α : Type u)
extends Protorder α, IsTrans α HasEquiv.Equiv

namespace IsEquivTrans
  variable [self : IsEquivTrans α]

  theorem equiv_trans : ∀ {a b c : α}, a ≈ b → b ≈ c → a ≈ c :=
    Trans.trans
end IsEquivTrans



class QPreorder (α : Type u)
extends IsLTTrans α, IsRefl α LE.le

namespace QPreorder
  variable [self : QPreorder α]

  @[simp]
  theorem le_refl {a : α} : a ≤ a :=
    self.refl _

  instance instWellFounded [Finite α] : WellFoundedLT α :=
    ⟨Finite.wellFounded_of_trans_of_irrefl self.lt⟩

  def wellFounded [Finite α] := self.instWellFounded
end QPreorder



class QOrder (α : Type u)
extends QPreorder α, IsTotal α LE.le

namespace QOrder
  variable [self : QOrder α]

  @[simp]
  theorem le_total {a b : α} : a ≤ b ∨ b ≤ a :=
    self.total a b

  instance instWellFounded [Finite α] : WellFoundedLT α :=
    ⟨Finite.wellFounded_of_trans_of_irrefl self.lt⟩

  def wellFounded [Finite α] := self.instWellFounded
end QOrder



namespace Protorder
  variable [self : Protorder α]

  scoped instance instPreorder [R : IsRefl α self.le] [T : IsTrans α self.le] : Preorder α where
    le := self.le
    lt := self.lt
    le_refl := R.refl
    le_trans := T.trans
    lt_iff_le_not_le _ _ := self.lt_def

  def toPreorder := @instPreorder

  def mkPreorder (le_refl : Reflexive self.le) (le_trans : Transitive self.le) :=
    instPreorder (R := ⟨le_refl⟩) (T := ⟨le_trans⟩)

  scoped instance instSelfOfPreorder
    [P : Preorder α]
  : Protorder α := {
    toLE := P.toLE
    toLT := P.toLT
    lt_def' := P.lt_iff_le_not_le
  }

  def ofPreorder := @instSelfOfPreorder

end Protorder



/-- A `Preorder` with a total `≤`. -/
class Order (α : Type u) extends Preorder α, IsTotal α LE.le

namespace Order
  variable [self : Order α]

  def le_total {a b : α} : a ≤ b ∨ b ≤ a :=
    self.total a b

  instance instQPreorder : QPreorder α where

  def toQPreorder := self.instQPreorder

  instance instQOrder : QOrder α where

  def toQOrder := self.instQOrder

  instance instPartialOrder [A : IsAntisymm α self.le] : PartialOrder α where
    le_antisymm a b := A.antisymm a b

  def toPartialOrder [IsAntisymm α self.le] := self.instPartialOrder
end Order
