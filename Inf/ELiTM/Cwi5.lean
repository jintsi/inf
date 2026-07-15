import Mathlib.Analysis.InnerProductSpace.Orthogonal

open scoped SetRel in
def SetRel.IsAntisymm (R : SetRel α α) := Std.Antisymm (· ~[R] ·)

namespace Elitm.Cwi5.Zad1

inductive A where
| a
| b
| c
| d
| e

open A in
def R : SetRel A A := {(a, a), (a, b), (b, c), (b, d), (a, d), (c, d), (e, e), (a, c), (e, d)}

theorem R_refl : ¬R.IsRefl := by intro; simpa [R] using R.refl A.b
theorem R_symm : ¬R.IsSymm := by intro; simpa [R] using R.comm (a := A.a) (b := A.b)
theorem R_trans : R.IsTrans where
  trans := by simp +contextual [R, or_imp]
theorem R_antisymm : R.IsAntisymm where
  antisymm := by simp +contextual [R, or_imp]
theorem R_irrefl : ¬R.IsIrrefl := by intro; simpa [R] using R.irrefl A.a

end Zad1

namespace Zad2

theorem Eq_refl (α : Sort*) : @Std.Refl α Eq := inferInstance
theorem Eq_symm (α : Sort*) : @Std.Symm α Eq := inferInstance
theorem Eq_trans (α : Sort*) : IsTrans α Eq := inferInstance
theorem Eq_antisymm (α : Sort*) : @Std.Antisymm α Eq where
  antisymm _ _ h _ := h

alias Ne_symm := instSymmNe_mathlib
theorem Ne_irrefl (α : Sort*) : @Std.Irrefl α Ne where
  irrefl _ := Ne.irrefl

alias LT_trans := instIsTransLt
alias LT_antisymm := instAntisymmLt
alias LT_irrefl := instIrreflLt

alias LE_refl := instReflLe
alias LE_trans := instIsTransLe
alias LE_antisymm := instAntisymmLe

theorem Subset_refl (α : Type*) : @Std.Refl (Set α) (· ⊆ ·) := LE_refl
theorem Subset_trans (α : Type*) : IsTrans (Set α) (· ⊆ ·) := LE_trans
theorem Subset_antisymm (α : Type*) : @Std.Antisymm (Set α) (· ⊆ ·) := LE_antisymm

alias Dvd_refl := instReflDvd_mathlib
alias Dvd_trans := instIsTransDvd
theorem Dvd_antisymm [CommMonoidWithZero α] [IsCancelMulZero α] [Subsingleton αˣ] :
    @Std.Antisymm α (· ∣ ·) where
  antisymm _ _ := dvd_antisymm

alias Parallel_refl := AffineSubspace.instReflParallel
alias Parallel_symm := AffineSubspace.instSymmParallel
alias Parallel_trans := AffineSubspace.instIsTransParallel

alias Ortho_symm := Submodule.symmetric_isOrtho

alias empty_symm := SetRel.isSymm_empty
alias empty_trans := SetRel.isTrans_empty
theorem empty_antisymm : (∅ : SetRel α α).IsAntisymm where
  antisymm := by simp
theorem empty_irrefl : (∅ : SetRel α α).IsIrrefl where
  irrefl := by simp

alias univ_refl := SetRel.isRefl_univ
alias univ_symm := SetRel.isSymm_univ
alias univ_trans := SetRel.isTrans_univ

def A [Semiring R] (x y : R) := 2 ∣ x + y

theorem A_refl [Semiring R] : @Std.Refl R A where
  refl a := by rw [A, ← two_mul]; exact dvd_mul_right 2 a
theorem A_symm [Semiring R] : @Std.Symm R A where
  symm a b h := by simpa [A, add_comm] using h
theorem A_trans [Ring R] : IsTrans R A where
  trans a b c := by simp [A]; intro ha hc; convert (ha.add hc).sub (dvd_mul_right 2 b); noncomm_ring

theorem B_symm [Semiring R] : Std.Symm fun x y : R => 3 ∣ x + y where
  symm a b h := by simpa [A, add_comm] using h

def M [Ring R] (n x y : R) := n ∣ x - y

theorem M_refl [Ring R] : @Std.Refl R (M n) where
  refl a := by simp [M]
theorem M_symm [Ring R] : @Std.Symm R (M n) where
  symm a b h := by simpa [M] using h.neg_right
theorem M_trans [Ring R] : IsTrans R (M n) where
  trans a b c ha hc := by simpa [M] using ha.add hc

theorem D_symm [NonAssocCommSemiring R] : @Std.Symm R fun x y => x * y = 4 where
  symm a b h := mul_comm a b ▸ h

def E [Ring R] [LinearOrder R] [FloorRing R] (x y : R) := ⌊x⌋ = ⌊y⌋

theorem E_refl [Ring R] [LinearOrder R] [FloorRing R] : @Std.Refl R E where
  refl _ := rfl
theorem E_symm [Ring R] [LinearOrder R] [FloorRing R] : @Std.Symm R E where
  symm _ _ := Eq.symm
theorem E_trans [Ring R] [LinearOrder R] [FloorRing R] : IsTrans R E where
  trans _ _ _ := Eq.trans

end Zad2

theorem Zad4a : ¬Equivalence fun x y : ℤ => Even (x * y) := by intro h; simpa using h.refl 1

theorem Zad4b : ¬Equivalence fun x y : ℤ => Odd (x * y) := by intro h; simpa using h.refl 0

theorem Zad4c [DivisionRing R] : ¬Equivalence fun (x y : R) => ∃ q : ℚ, x * q = y := by
  intro h; simpa using @h.symm 1 0 ⟨0, by simp⟩

theorem Zad4d : Equivalence fun x y : ℝ => ∃ a b : ℚ, x - y = a + b * √2 where
  refl _ := ⟨0, 0, by simp⟩
  symm := fun ⟨a, b, h⟩ => ⟨-a, -b, by simp [← neg_add, -neg_add_rev, ← h]⟩
  trans := fun ⟨a, b, h₁⟩ ⟨c, d, h₂⟩ =>
    ⟨a + c, b + d, by convert congr($h₁ + $h₂) using 1 <;> simp; ring⟩

theorem Zad4e : Equivalence fun s t : Set α => (symmDiff s t).Finite where
  refl _ := by simp
  symm _ := by rwa [symmDiff_comm]
  trans h₁ h₂ := h₁.symmDiff_congr.mpr h₂

theorem _root_.Finset.card_symmDiff [DecidableEq α] {s t : Finset α} :
    (symmDiff s t).card = s.card + t.card - 2 * (s ∩ t).card := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff, Finset.card_sdiff,
    Finset.card_sdiff, Finset.inter_comm, two_mul, tsub_add_tsub_comm] <;> (gcongr; simp)

lemma _root_.Finset.even_card_symmDiff_iff [DecidableEq α] {s t : Finset α} :
    Even (symmDiff s t).card ↔ Even (s.card + t.card) := by
  rw [Finset.card_symmDiff, Nat.even_sub]; simp
  rw [two_mul]; gcongr <;> simp

theorem Zad4f [DecidableEq α] : Equivalence fun s t : Finset α => Even (symmDiff s t).card where
  refl _ := by simp
  symm _ := by rwa [symmDiff_comm]
  trans h₁ h₂ := by simp_all [Finset.even_card_symmDiff_iff, Nat.even_add]

theorem Zad4g [Nonempty α] : ¬Equivalence fun s t : Set α => s ∩ t = ∅ := by
  intro h; simpa using @h.trans {Classical.arbitrary α} ∅ {Classical.arbitrary α}

theorem Zad4h [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ¬Equivalence fun x y : K => |x - y| < 1 := by
  intro h; simpa [-one_div, sub_self_div_two, abs_one_div] using @h.trans 1 (1 / 2) 0

theorem Zad4i [Add α] [Pow α ℕ] :
    Equivalence fun a b : α × α => a.1 ^ 2 + a.2 ^ 2 = b.1 ^ 2 + b.2 ^ 2 := eq_equivalence.comap _

theorem Zad4j [Nonempty α] : ¬Equivalence fun s t : Set α => s \ t = Set.univ := by
  intro h; simpa [Set.empty_ne_univ] using h.refl

theorem Zad4k : ¬Equivalence fun s t : Set α => u ⊂ s ∩ t := by
  intro h; simpa [Set.ssubset_def] using h.refl ∅

open Polynomial in
theorem Zad4l [Semiring R] [Nontrivial R] : ¬Equivalence fun p q : R[X] => Even (p * q).degree := by
  intro h; convert @h.trans 1 0 X; simp [Even]; use ⟨⊥, rfl⟩; intro
  | ⊥ => simp
  | (n : ℕ) => norm_cast; omega

theorem Zad5 (hr : Equivalence r) (hs : Equivalence s) : Equivalence (r ⊓ s) where
  refl x := ⟨hr.refl x, hs.refl x⟩
  symm := fun ⟨h₁, h₂⟩ => ⟨hr.symm h₁, hs.symm h₂⟩
  trans := fun ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => ⟨hr.trans h₁ h₃, hs.trans h₂ h₄⟩

theorem Zad7_eq : Relation.Comp (α := α) Eq Eq = Eq := Relation.comp_eq

theorem Zad7_lt [Preorder α] [DenselyOrdered α] : Relation.Comp (α := α) (· < ·) (· < ·) = (· < ·) := by
  ext x y; constructor
  · simp [Relation.Comp]; exact fun _ => lt_trans
  · exact exists_between

theorem Zad9 (hr : @Std.Refl α r) : IsTrans α r ↔ Relation.Comp r r = r := by
  constructor
  · intro h; ext x y; constructor
    · intro ⟨z, hx, hy⟩; exact h.trans x z y hx hy
    · intro hxy; use x, refl x
  · simp [funext_iff]; intro h; constructor; intro a b c ha hc; rw [← h]; use b

alias Zad10 := flip_eq_iff

theorem Zad11_flip {α : Type*} {r : α → α → Prop} (hr : Equivalence r) : Equivalence (flip r) :=
  Zad10.mpr hr.stdSymm ▸ hr

theorem Zad11_comp (hr : Equivalence r) : Equivalence (Relation.Comp r r) :=
  ((Zad9 hr.stdRefl).mp hr.isTrans).symm ▸ hr

alias Zad13_refl := Subrel.instReflSubtype
alias Zad13_symm := Subrel.instSymmSubtype
alias Zad13_trans := Subrel.instIsTransSubtype
theorem Zad13_antisymm (r : α → α → Prop) [Std.Antisymm r] (p : α → Prop) :
    Std.Antisymm (Subrel r p) := ⟨fun _ _ h h' => Subtype.ext (antisymm (α := α) h h')⟩

alias Zad14 := Relation.transGen_minimal
