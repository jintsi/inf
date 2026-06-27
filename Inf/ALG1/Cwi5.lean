import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.ZMod.Basic

/-! # Some notes from `Mathlib/Algebra/Module/Defs.lean`:

in Mathlib, the way of saying that `V` is a vector space over `K` is:
`[Field K] [AddCommGroup V] [Module K V]`.

A module is just a vector space with less axioms required from `K` and `V` separately,
which is why the same typeclass is used for both - and why `K` and `V` are typically notated
`R` and `M` instead, i.e. `[Semiring R] [AddCommMonoid M] [Module R M]`. -/

/-- A subset of a module (vector space) is a submodule (subspace) iff it contains the origin and
is closed under addition and scalar multiplication. -/
structure IsSubmodule (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    (s : Set M) : Prop where
  zero_mem : 0 ∈ s
  add_mem : a ∈ s → b ∈ s → a + b ∈ s
  smul_mem (c : R) {x : M} : x ∈ s → c • x ∈ s

namespace ALG1.Cwi5

theorem Zad1a : ¬IsSubmodule ℝ {(x, _, _) : ℝ × ℝ × ℝ | x ≠ 0} := by
  simp [mt IsSubmodule.zero_mem]

theorem Zad1b [Semiring R] : IsSubmodule R {(x, y, z) : R × R × R | x + 3 * y = z} := by
  apply IsSubmodule.mk <;>
    simp +contextual [mul_add, ← add_assoc, add_right_comm _ _ (_ * _)]
  simp [(show (3 : R) = 1 + 1 + 1 by norm_num), add_mul, mul_add]

theorem Zad1c : ¬IsSubmodule ℝ {(x, y, _) : ℝ × ℝ × ℝ | y = x ^ 2} :=
 fun this => by simpa [sq] using this.smul_mem 2 (show (1, 1, 1) ∈ _ by simp)

theorem Zad1d : ¬IsSubmodule ℝ {(x, _, z) : ℝ × ℝ × ℝ | x * z = 0} :=
 fun this => by simpa using this.add_mem (a := (1, 0, 0)) (b := (0, 0, 1))

theorem Zad1e [Semiring R] : IsSubmodule R {(x, y, z) : R × R × R | x = 0 ∧ y = 2 * z} := by
  apply IsSubmodule.mk <;> simp +contextual [mul_add]; simp [two_mul, mul_add]

theorem Zad1f [Semiring R] : IsSubmodule R {(a, b) : R × R | a + b = 0} := by
  apply IsSubmodule.mk <;> simp +contextual [add_add_add_comm, ← mul_add]

theorem Zad1g : ¬IsSubmodule ℝ {(a, b, c) : ℝ × ℝ × ℝ | 4 * a + 2 * b + c = 1} :=
 fun this => by simpa using this.zero_mem

theorem Zad1h : ¬IsSubmodule ℝ {(a, b, c) : ℝ × ℝ × ℝ | (a + b + c) * c = 0} :=
 fun this => by simpa using this.add_mem (a := (0, -1, 1)) (b := (0, 1, 0))

theorem Zad4 [Semiring R] [AddCommMonoid M] [Module R M] {M₁ M₂ : Set M} :
    IsSubmodule R M₁ → IsSubmodule R M₂ → IsSubmodule R (M₁ ∩ M₂) := by
  intro h1 h2; apply IsSubmodule.mk
  · simp [h1.zero_mem, h2.zero_mem]
  · simp +contextual [h1.add_mem, h2.add_mem]
  · simp +contextual [h1.smul_mem, h2.smul_mem]

theorem Zad5a : (![0, -2, 1] : _ → ℚ) =
    (-1) • ![2, 0, 1] + (-3) • ![1, 1, 0] + 1 • ![5, 1, 2] := by norm_num

theorem Zad5b : ¬∃ a b c : ℚ, (![1, 1, 1] : _ → ℚ) =
    a • ![2, 0, 1] + b • ![1, 1, 0] + c • ![5, 1, 2] := by simp; grind only

theorem Zad5c : (![1, -1, 3] : _ → ℚ) =
    (7/5 : ℚ) • ![2, 0, 1] + (-9/5 : ℚ) • ![1, 1, 0] + (4/5 : ℚ) • ![0, 1, 2] := by norm_num

theorem Zad6 : (![3, -1, 0, -1] : _ → ℚ ) ∉
    Submodule.span ℚ {![3, -1, 3, 2], ![-1, 1, 1, -3], ![1, 1, 9, -5]} := by
  simp [Submodule.mem_span_triple]; intros; linarith

open Polynomial in
theorem Zad7 : (X ^ 2 + 1 : ℤ[X]) ∈ Submodule.span ℤ {X, X ^ 2 - 3, X + 2, X - 1} := by
  simp [Submodule.mem_span_insert, Submodule.mem_span_singleton]; exists -2, 1, 2, 0; ring

open Polynomial in
theorem ZadD1a [Semiring R] (r : R) : IsSubmodule R {p : R[X] | p.IsRoot r} := by
  apply IsSubmodule.mk <;> simp +contextual

theorem ZadD2a [Ring R] [LinearOrder R] [IsOrderedRing R] :
    IsSubmodule R {f : ℕ → R | BddAbove (Set.range f) ∧ BddBelow (Set.range f)} where
  zero_mem := by simp
  add_mem := by simp +contextual [Pi.add_def, BddAbove.range_add, BddBelow.range_add]
  smul_mem := by
    simp [Pi.smul_def, Set.range_mul]; intro c x ha hb; cases le_total 0 c
    · exact ⟨ha.smul_of_nonneg ‹_›, hb.smul_of_nonneg ‹_›⟩
    · exact ⟨hb.smul_of_nonpos ‹_›, ha.smul_of_nonpos ‹_›⟩

open Topology Filter in
theorem ZadD2b [Semiring R] [TopologicalSpace R] [ContinuousAdd R] [SeparatelyContinuousMul R] :
    IsSubmodule R {f : ℕ → R | ∃ g, Tendsto f atTop (𝓝 g)} where
  zero_mem := ⟨0, tendsto_const_nhds⟩
  add_mem := fun ⟨ga, ha⟩ ⟨gb, hb⟩ => ⟨ga + gb, ha.add hb⟩
  smul_mem := fun c _ ⟨g, h⟩ => ⟨c * g, h.const_mul c⟩

open Topology Filter in
theorem ZadD2c [Semiring R] [TopologicalSpace R] [ContinuousAdd R] [SeparatelyContinuousMul R] :
    IsSubmodule R {f : ℕ → R | Tendsto f atTop (𝓝 0)} where
  zero_mem := tendsto_const_nhds
  add_mem := fun ha hb => by simpa using! Tendsto.add ha hb
  smul_mem := fun c a h => by simpa using! Tendsto.const_mul c h

open Topology Filter in
theorem ZadD2d : ¬IsSubmodule ℝ {f : ℕ → ℝ | Tendsto f atTop (𝓝 1)} :=
  fun this => one_ne_zero (tendsto_nhds_unique this.zero_mem tendsto_const_nhds)

theorem ZadD2e [Semiring R] : IsSubmodule R (Set.range Finsupp.toFun : Set (ℕ → R)) where
  zero_mem := ⟨0, rfl⟩
  add_mem := by rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩; exists f + g
  smul_mem := by rintro c _ ⟨f, rfl⟩; exists c • f

theorem ZadD3b [TopologicalSpace X] [Semiring R] [TopologicalSpace R] [ContinuousAdd R]
    [SeparatelyContinuousMul R] : IsSubmodule R {f : X → R | Continuous f} where
  zero_mem := continuous_zero
  add_mem := Continuous.add
  smul_mem c _ h := h.const_smul c

theorem ZadD3c [NontriviallyNormedField K] [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] : IsSubmodule K {f : E → F | Differentiable K f} where
  zero_mem := differentiable_zero
  add_mem := Differentiable.add
  smul_mem c _ h := h.const_smul c

local instance ZadD4_group {T : Type u} : AddCommGroup (Set T) where
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
local instance Zad5_D4 {T : Type u} : Module (ZMod 2) (Set T) where
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
    intro a b s; fin_cases a <;> fin_cases b <;> norm_num <;>
      first | exact zero_smul ℕ s | exact (one_smul ℕ _).symm

alias ZadD5a := smul_eq_zero
alias ZadD5b1 := neg_smul
alias ZadD5b2 := smul_neg
alias ZadD5c := neg_one_smul
