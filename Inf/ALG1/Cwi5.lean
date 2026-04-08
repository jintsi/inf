import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.ZMod.Basic

/-! # Some notes from `Mathlib/Algebra/Module/Defs.lean`:

in Mathlib, the way of saying that `V` is a vector space over `K` is:
`[Field K] [AddCommGroup V] [Module K V]`.

A module is just a vector space with less axioms required from `K` and `V` separately,
which is why the same typeclass is used for both - and why `K` and `V` are typically notated
`R` and `M` instead, i.e. `[Semiring R] [AddCommMonoid M] [Module R M]`. -/

class IsSubmodule (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M] (s : Set M) : Prop where
  zero_mem : 0 ∈ s
  add_mem : a ∈ s → b ∈ s → a + b ∈ s
  smul_mem (c : R) {x : M} : x ∈ s → c • x ∈ s

namespace ALG1

theorem Zad5_1a : ¬IsSubmodule ℝ {(x, _, _) : ℝ × ℝ × ℝ | x ≠ 0} := by
  by_contra!; simpa using this.zero_mem

theorem Zad5_1b : IsSubmodule ℝ {(x, y, z) : ℝ × ℝ × ℝ | x + 3 * y = z} := by
  apply IsSubmodule.mk <;> simp <;> grind

theorem Zad5_1c : ¬IsSubmodule ℝ {(x, y, _) : ℝ × ℝ × ℝ | y = x ^ 2} := by
  intro this
  have h := this.smul_mem 2 (show (1, 1, 1) ∈ _ by simp)
  simp at h; linarith

theorem Zad5_1d : ¬IsSubmodule ℝ {(x, _, z) : ℝ × ℝ × ℝ | x * z = 0} := by
  intro this; simpa using this.add_mem (a := (1, 0, 0)) (b := (0, 0, 1))

theorem Zad5_1e : IsSubmodule ℝ {(x, y, z) : ℝ × ℝ × ℝ | x = 0 ∧ y = 2 * z} := by
  apply IsSubmodule.mk <;> simp <;> grind

theorem Zad5_1f : IsSubmodule ℝ {(a, b) : ℝ × ℝ | a + b = 0} := by
  apply IsSubmodule.mk <;> simp <;> grind

theorem Zad5_1g : ¬IsSubmodule ℝ {(a, b, c) : ℝ × ℝ × ℝ | 4 * a + 2 * b + c = 1} := by
  intro this; simpa using this.zero_mem

theorem Zad5_1h : ¬IsSubmodule ℝ {(a, b, c) : ℝ × ℝ × ℝ | (a + b + c) * c = 0} := by
  intro this; simpa using this.add_mem (a := (0, -1, 1)) (b := (0, 1, 0))

theorem Zad5_4 [Semiring R] [AddCommMonoid M] [Module R M] {M₁ M₂ : Set M} :
    IsSubmodule R M₁ → IsSubmodule R M₂ → IsSubmodule R (M₁ ∩ M₂) := by
  intro h1 h2
  apply IsSubmodule.mk
  · simp [h1.zero_mem, h2.zero_mem]
  · simp; intro a b ha1 ha2 hb1 hb2; exact ⟨h1.add_mem ha1 hb1, h2.add_mem ha2 hb2⟩
  · simp; intros; and_intros <;> apply IsSubmodule.smul_mem <;> assumption

theorem Zad5_5a : (![0, -2, 1] : _ → ℚ) = (-1) • ![2, 0, 1] + (-3) • ![1, 1, 0] + 1 • ![5, 1, 2] := by norm_num
theorem Zad5_5b : ¬∃ a b c : ℚ, (![1, 1, 1] : _ → ℚ) = a • ![2, 0, 1] + b • ![1, 1, 0] + c • ![5, 1, 2] := by
  simp; grind
theorem Zad5_5c : (![1, -1, 3] : _ → ℚ) = (7/5 : ℚ) • ![2, 0, 1] +
    (-9/5 : ℚ) • ![1, 1, 0] + (4/5 : ℚ) • ![0, 1, 2] := by norm_num

theorem Zad5_6 : (![3, -1, 0, -1] : _ → ℚ ) ∉ Submodule.span ℚ {![3, -1, 3, 2], ![-1, 1, 1, -3], ![1, 1, 9, -5]} := by
  simp [Submodule.mem_span_triple]; intro a b c h1 h2 h3; linarith

open Polynomial in
theorem Zad5_7 : (X ^ 2 + 1 : ℤ[X]) ∈ Submodule.span ℤ {X, X ^ 2 - 3, X + 2, X - 1} := by
  simp_rw [Submodule.mem_span_insert, Submodule.mem_span_singleton]; simp
  exists -2, 1, 2, 0; grind

theorem Zad5_D2a : IsSubmodule ℝ {f : ℕ → ℝ | BddAbove (Set.range f) ∧ BddBelow (Set.range f)} where
  zero_mem := by simp
  add_mem := by
    simp [Pi.add_def]; intros; and_intros
    · apply BddAbove.range_add <;> assumption
    · apply BddBelow.range_add <;> assumption
  smul_mem := by
    simp [Pi.smul_def, Set.range_mul]; intro c x ha hb
    cases le_total 0 c
    · exact ⟨BddAbove.smul_of_nonneg ha ‹_›, BddBelow.smul_of_nonneg hb ‹_›⟩
    · exact ⟨BddBelow.smul_of_nonpos ‹_› hb, BddAbove.smul_of_nonpos ‹_› ha⟩

open Topology Filter in
theorem Zad5_D2b : IsSubmodule ℝ {f : ℕ → ℝ | ∃ g, Tendsto f atTop (𝓝 g)} where
  zero_mem := ⟨0, tendsto_const_nhds⟩
  add_mem := fun ⟨ga, ha⟩ ⟨gb, hb⟩ => ⟨ga + gb, ha.add hb⟩
  smul_mem := fun c _ ⟨g, h⟩ => ⟨c * g, h.const_mul c⟩

open Topology Filter in
theorem Zad5_D2c : IsSubmodule ℝ {f : ℕ → ℝ | Tendsto f atTop (𝓝 0)} where
  zero_mem := tendsto_const_nhds
  add_mem := fun ha hb => by simpa using Tendsto.add ha hb
  smul_mem := fun c a h => by simpa using Tendsto.const_mul c h

open Topology Filter in
theorem Zad5_D2d : ¬IsSubmodule ℝ {f : ℕ → ℝ | Tendsto f atTop (𝓝 1)} :=
  fun this => one_ne_zero (tendsto_nhds_unique this.zero_mem tendsto_const_nhds)

theorem Zad5_D2e : IsSubmodule ℝ (Set.range Finsupp.toFun : Set (ℕ → ℝ)) where
  zero_mem := ⟨0, rfl⟩
  add_mem := by simp; intros; subst_vars; rename_i f g; exists f + g
  smul_mem := by simp; intro c f; exists c • f
theorem Zad5_D3b : IsSubmodule ℝ {f : ℝ → ℝ | Continuous f} where
  zero_mem := continuous_zero
  add_mem := Continuous.add
  smul_mem c _ h := Continuous.const_smul h c
theorem Zad5_D3c : IsSubmodule ℝ {f : ℝ → ℝ | Differentiable ℝ f} where
  zero_mem := differentiable_zero
  add_mem := Differentiable.add
  smul_mem c _ h := Differentiable.const_mul h c

instance Zad5_D4_group {T : Type u} : AddCommGroup (Set T) where
  add := symmDiff
  add_comm := symmDiff_comm
  add_assoc := symmDiff_assoc
  zero := ∅
  zero_add := by simp [← Add.add_eq_hAdd]; rfl
  add_zero := by simp [← Add.add_eq_hAdd]; rfl
  neg := id
  neg_add_cancel := by simp [← Add.add_eq_hAdd]; rfl
  nsmul := @nsmulRec _ ⟨∅⟩ ⟨symmDiff⟩
  zsmul := @zsmulRec _ ⟨∅⟩ ⟨symmDiff⟩ ⟨id⟩ (@nsmulRec _ ⟨∅⟩ ⟨symmDiff⟩)

set_option backward.isDefEq.respectTransparency false in
instance Zad5_D4 {T : Type u} : Module (ZMod 2) (Set T) where
  smul a s := a.val • s
  smul_zero := fun a => smul_zero a.val
  smul_add := fun a => smul_add a.val
  zero_smul := zero_smul ℕ
  add_smul := by
    intro a b s
    fin_cases a <;> fin_cases b <;> norm_num <;> try exact zero_smul ℕ s
    nth_rw 6 [← Nat.cast_ofNat]; rw [ZMod.natCast_self 2]
    simp [← Add.add_eq_hAdd, Add.add]; exact zero_smul ℕ s
  one_smul := one_smul ℕ
  mul_smul := by
    intro a b s
    fin_cases a <;> fin_cases b <;> norm_num <;> first | exact zero_smul ℕ s | exact (one_smul ℕ _).symm

alias Zad5_D5a := smul_eq_zero

alias Zad5_D5b1 := neg_smul

alias Zad5_D5b2 := smul_neg

theorem Zad5_D5c [Ring R] [AddCommGroup M] [Module R M] (v : M) : -1 • v = -v := by
  rw [neg_smul, one_smul]
