import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Matrix.Reflection

open LinearMap Submodule

namespace ALG1.Cwi8

set_option linter.unusedVariables false in
theorem Zad1a [Semiring R] : IsLinearMap R fun ((x₁, x₂, x₃) : R × R × R) => (x₁, x₂) :=
  isLinear ((LinearMap.fst _ _ _).prod (fst _ _ _ ∘ₗ snd _ _ _))

theorem Zad1b : ¬IsLinearMap ℝ fun ((x₁, x₂) : ℝ × ℝ) => x₁ * x₂ :=
  fun h => by simpa [self_eq_neg] using h.map_neg 1

theorem Zad1c [Ring R] : IsLinearMap R fun ((x, y, z) : R × R × R) => (2 * x - 2 * y, z - x, y - x) where
  map_add x y := by dsimp; noncomm_ring
  map_smul c x := by dsimp; noncomm_ring

open Polynomial in
theorem Zad1d [CommRing R] : IsLinearMap R fun (p : R[X]) => derivative^[2] ((X ^ 2 - X - 1) * p) where
  map_add p q := by simp [-derivative_mul, mul_add]
  map_smul c p := by simp [-derivative_mul]

theorem Zadf : ¬IsLinearMap ℝ fun ((x, y) : ℝ × ℝ) => (x + 1, 2 * y, x + y) :=
  fun h => by simpa using h.map_zero

theorem Zad1g [CommSemiring R] [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    IsLinearMap R fun X : Matrix n n R => X * A + A * X :=
  isLinear (mulRight R A + mulLeft R A)

theorem Zad2a : (fun (x : Fin 3 → ℝ) => (2 * x 0 - x 1, 3 * x 0 + x 1 - x 2)) =
    Matrix.toLin (Pi.basisFun ℝ (Fin 3)) (Module.Basis.finTwoProd ℝ) !![2, -1, 0; 3, 1, -1] := by
  ext x
  · simp [Matrix.toLin_apply, Matrix.vecHead, Matrix.vecTail, sub_eq_add_neg]
  · simp [Matrix.toLin_apply, Matrix.vecHead, Matrix.vecTail, sub_eq_add_neg, add_assoc]

theorem Zad2b (α : ℝ) : (rotation (Real.Angle.toCircle α)).toMatrix
    Complex.basisOneI Complex.basisOneI = !![α.cos, -α.sin; α.sin, α.cos] := by
  rw [toMatrix_rotation]; simp

theorem Zad3a [CommRing R] : (fun (x : Fin 4 → R) => ![2 * x 0 + x 2, 2 * x 1 - x 3, x 2 + 2 * x 3]) =
    Matrix.toLin' !![2, 0, 1, 0; 0, 2, 0, -1; 0, 0, 1, 2] := by
  simp [funext_iff, Fin.forall_fin_succ_pi, sub_eq_add_neg]

theorem Zad3a_ker [Field R] [CharZero R] :
    (Matrix.toLin' !![2, 0, 1, 0; 0, 2, 0, -1; 0, 0, 1, 2]).ker = R ∙ ![2, 1, -4, 2] := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, mem_span_singleton]; grind only

theorem Zad3a_range [Field R] [CharZero R] :
    (Matrix.toLin' !![2, 0, 1, 0; 0, 2, 0, -1; 0, 0, 1, 2]).range = (⊤ : Submodule R _) := by
  simp [eq_top_iff', Fin.forall_fin_succ_pi, Fin.exists_fin_succ_pi]
  intro x y z; use (x - z) / 2, y / 2, z, (by ring), 0, (by ring), by simp

theorem Zad3b [CommRing R] :
    (fun (x : Fin 3 → R) => ![x 0 + x 1 + 2 * x 2, x 0 - 2 * x 1 + 2 * x 2, 2 * x 0 - x 1 + 4 * x 2, x 0 + 2 * x 1 + 2 * x 2])
    = Matrix.toLin' !![1, 1, 2; 1, -2, 2; 2, -1, 4; 1, 2, 2] := by
  simp [funext_iff, Fin.forall_fin_succ_pi, ← add_assoc, sub_eq_add_neg]

theorem Zad3b_ker [Field R] :
    (Matrix.toLin' !![1, 1, 2; 1, -2, 2; 2, -1, 4; 1, 2, 2]).ker = R ∙ ![-2, 0, 1] := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, mem_span_singleton]; grind only

theorem Zad3b_range [CommRing R] :
    (Matrix.toLin' !![1, 1, 2; 1, -2, 2; 2, -1, 4; 1, 2, 2]).range = span R {![1, 1, 2, 1], ![1, -2, -1, 2]} := by
  simp [Submodule.ext_iff, Fin.exists_fin_succ_pi, mem_span_pair]
  intro x; constructor
  · rintro ⟨x, y, z, rfl⟩; use x + 2 * z, y; ring_nf
  · rintro ⟨a, b, rfl⟩; use a, b, 0; simp [mul_comm]

theorem Zad3c [CommRing R] :
    (fun (x : Fin 4 → R) => ![x 0 + 2 * x 1 + 3 * x 2 - x 3, 0, x 0 - x 1 + 2 * x 3, x 1 + x 2 - x 3])
    = Matrix.toLin' !![1, 2, 3, -1; 0, 0, 0, 0; 1, -1, 0, 2; 0, 1, 1, -1] := by
  simp [funext_iff, Fin.forall_fin_succ_pi, ← add_assoc, sub_eq_add_neg]

theorem Zad3c_ker [Field R] [CharZero R] :
    (Matrix.toLin' !![1, 2, 3, -1; 0, 0, 0, 0; 1, -1, 0, 2; 0, 1, 1, -1]).ker =
    span R {![-1, 1, 0, 1], ![-2, 0, 1, 1]} := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, mem_span_pair]; grind only

theorem Zad3c_range [CommRing R] :
    (Matrix.toLin' !![1, 2, 3, -1; 0, 0, 0, 0; 1, -1, 0, 2; 0, 1, 1, -1]).range =
    span R {![1, 0, 1, 0], ![2, 0, -1, 1]} := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, Fin.exists_fin_succ_pi, mem_span_pair]
  intro x y z w; constructor
  · rintro ⟨x, y, z, w, rfl, rfl, rfl, rfl⟩; use x + z + w; ring_nf; tauto
  · rintro ⟨x, rfl, rfl, rfl⟩; use x, w, 0, 0; simp [mul_comm]

theorem Zad3d [CommRing R] :
    (fun (x : Fin 4 → R) => ![2 * x 0 + x 1 - x 2 + 3 * x 3, 4 * x 0 + 2 * x 1 - 2 * x 2 + 6 * x 3, -2 * x 0 - x 1 + x 2 - 3 * x 3])
    = Matrix.toLin' !![2, 1, -1, 3; 4, 2, -2, 6; -2, -1, 1, -3] := by
  simp [funext_iff, Fin.forall_fin_succ_pi, ← add_assoc, sub_eq_add_neg]

theorem Zad3d_ker [CommRing R] :
    (Matrix.toLin' !![2, 1, -1, 3; 4, 2, -2, 6; -2, -1, 1, -3]).ker =
    span R {![1, 0, 2, 0], ![0, 1, 1, 0], ![0, 0, 3, 1]} := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, mem_span_triple]; grind only

theorem Zad3d_range [CommRing R] :
    (Matrix.toLin' !![2, 1, -1, 3; 4, 2, -2, 6; -2, -1, 1, -3]).range = R ∙ ![1, 2, -1] := by
  simp [Submodule.ext_iff, Fin.exists_fin_succ_pi, mem_span_singleton]; intro x; constructor
  · rintro ⟨x, y, z, w, rfl, rfl, rfl⟩; use 2 * x + y - z + 3 * w; ring_nf
  · rintro ⟨v, rfl⟩; use 0, v, 0, 0; simp [mul_comm]

theorem Zad3e [CommSemiring R] : (fun (x : Fin 4 → R) => ![x 3, x 2, x 1, x 0]) =
    Matrix.toLin' !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
  simp [funext_iff, Fin.forall_fin_succ_pi]

theorem Zad3e_ker [CommSemiring R] :
    (Matrix.toLin' !![(0 : R), 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]).ker = ⊥ := by
  simp [Submodule.eq_bot_iff, Fin.forall_fin_succ_pi]

theorem Zad3e_range [CommSemiring R] :
    (Matrix.toLin' !![(0 : R), 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]).range = ⊤ := by
  simp [eq_top_iff', Fin.exists_fin_succ_pi, Fin.forall_fin_succ_pi]

theorem Zad3f [CommSemiring R] : (fun (x : Fin 4 → R) => ![x 0 + x 1 + 2 * x 3, 0, 2 * x 0 + x 2])
    = Matrix.toLin' !![1, 1, 0, 2; 0, 0, 0, 0; 2, 0, 1, 0] := by
  simp [funext_iff, Fin.forall_fin_succ_pi, add_assoc]

theorem Zad3f_ker [CommRing R] :
    (Matrix.toLin' !![1, 1, 0, 2; 0, 0, 0, 0; 2, 0, 1, 0]).ker = span R {![1, -1, -2, 0], ![0, -2, 0, 1]} := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, mem_span_pair]; grind only

theorem Zad3f_range [CommRing R] :
    (Matrix.toLin' !![1, 1, 0, 2; 0, 0, 0, 0; 2, 0, 1, 0]).range = span R {![1, 0, 0], ![0, 0, 1]} := by
  simp [Submodule.ext_iff, Fin.exists_fin_succ_pi, mem_span_pair]; intro v; constructor
  · rintro ⟨x, y, z, w, rfl⟩; simp
  · rintro ⟨a, b, rfl⟩; use 0, a, b, 0; simp

theorem Zad4 : ![5, -1, 0] ∈ !![1, 2, 3, 0; -1, 0, -1, 2; 2, -1, 1, 5].toLin'.range :=
  ⟨![1, 2, 0, 0], (Matrix.mulVecᵣ_eq _ _).symm⟩

theorem ZadD1a : IsLinearMap ℝ (starRingEnd ℂ) := Complex.conjAe.toLinearMap.isLinear

theorem ZadD1b : ¬IsLinearMap ℂ (starRingEnd ℂ) :=
  fun h => by simpa [_root_.neg_eq_self] using h.map_smul Complex.I 1

theorem ZadD2 [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
    (a : M₂) : IsLinearMap R (fun (_ : M₁) => a) ↔ a = 0 where
  mp h := h.map_zero
  mpr h := h ▸ isLinear 0

alias ZadD3 := IsLinearMap.map_zero

def ZadD4a (R) [CommRing R] : (Fin 5 → R) →ₗ[R] (Fin 3 → R) where
  toFun x := ![x 0 + 2 * x 1 +     x 2 - 3 * x 3 + 4 * x 4,
           2 * x 0 + 5 * x 1 + 4 * x 2 - 5 * x 3 + 5 * x 4,
               x 0 + 4 * x 1 + 5 * x 2 -     x 3 - 2 * x 4]
  map_add' x y := by simp; ring_nf; tauto
  map_smul' c x := by simp [mul_add, mul_sub, mul_left_comm]

@[simp]
lemma ZadD4a_apply [CommRing R] : ZadD4a R ![x, y, z, s, t] =
    ![x + 2 * y + z - 3 * s + 4 * t, 2 * x + 5 * y + 4 * z - 5 * s + 5 * t, x + 4 * y + 5 * z - s - 2 * t] := rfl

theorem ZadD4a_ker [Field R] [CharZero R] : (ZadD4a R).ker =
    span R {![5, 0, 0, 3, 1], ![0, 1, 0, 2, 1], ![0, 0, 5, 11, 7]} := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, mem_span_triple]; intro x y z s t; constructor
  case mpr => grind
  intro ⟨h1, h2, h3⟩; use x / 5, (by simp), z / 5, (by simp); grind

theorem ZadD4a_range [CommRing R] : (ZadD4a R).range = span R {![1, 2, 1], ![0, 1, 2]} := by
  simp [Submodule.ext_iff, Fin.exists_fin_succ_pi, mem_span_pair]; intro x; constructor
  · rintro ⟨x, y, z, s, t, rfl⟩; simp; use y + 2 * z + s - 3 * t; ring_nf; tauto
  · rintro ⟨a, b, rfl⟩; use a - 2 * b, b, 0, 0, 0; ring_nf

def ZadD4b (R) [CommRing R] : (Fin 3 → R) →ₗ[R] (Fin 3 → R) where
  toFun x := ![x 0 + 2 * x 1 - x 2, x 1 + x 2, x 0 + x 1 - 2 * x 2]
  map_add' x y := by simp; ring_nf; tauto
  map_smul' c x := by simp [mul_add, mul_sub, mul_left_comm]

@[simp]
lemma ZadD4b_apply [CommRing R] : ZadD4b R ![x, y, z] = ![x + 2 * y - z, y + z, x + y - 2 * z] := rfl

theorem ZadD4b_ker [CommRing R] : (ZadD4b R).ker = R ∙ ![3, -1, 1] := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, mem_span_singleton]; grind

theorem ZadD4b_range [CommRing R] : (ZadD4b R).range = span R {![1, 1, 0], ![1, 0, 1]} := by
  simp [Submodule.ext_iff, Fin.exists_fin_succ_pi, mem_span_pair]; intro v; constructor
  · rintro ⟨x, y, z, rfl⟩; simp; ring
  · rintro ⟨a, b, rfl⟩; use b - a, a, 0; simp; ring

theorem ZadD4c_ker [CommRing R] : (Matrix.toLin' !![1, 1; 1, 2]).ker = (⊥ : Submodule R _) := by
  simp [Submodule.eq_bot_iff, Fin.forall_fin_succ_pi]; grind

theorem ZadD4c_range [CommRing R] : (Matrix.toLin' !![1, 1; 1, 2]).range = (⊤ : Submodule R _) := by
  simp [eq_top_iff', Fin.exists_fin_succ_pi, Fin.forall_fin_succ_pi]
  intro a b; use 2 * a - b, b - a; ring_nf; tauto

theorem ZadD4d_ker [CommRing R] : (Matrix.toLin' !![1, 2; 3, 6]).ker = R ∙ ![-2, 1] := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, mem_span_singleton]; grind

theorem Zad4d_range [CommRing R] : (Matrix.toLin' !![1, 2; 3, 6]).range = R ∙ ![1, 3] := by
  simp [Submodule.ext_iff, Fin.exists_fin_succ_pi, mem_span_singleton]; intro v; constructor
  · rintro ⟨a, b, rfl⟩; simp; ring
  · rintro ⟨a, rfl⟩; use a, 0; simp [mul_comm]

theorem ZadD4e_ker [CommRing R] : (Matrix.toLin' !![0, 1, 1; 1, 1, 1; 1, 4, 5]).ker = (⊥ : Submodule R _) := by
  simp [Submodule.eq_bot_iff, Fin.forall_fin_succ_pi]; grind

theorem ZadD4e_range [CommRing R] : (Matrix.toLin' !![0, 1, 1; 1, 1, 1; 1, 4, 5]).range = (⊤ : Submodule R _) := by
  simp [eq_top_iff', Fin.exists_fin_succ_pi, Fin.forall_fin_succ_pi]; intro a b c
  use b - a, 4 * a + b - c, c - b - 3 * a; ring_nf; tauto

theorem ZadD4f_ker [Field R] [CharZero R] :
    (Matrix.toLin' !![2, 0, 0, 1; -1, 1, -2, 2; 2, 1, -5, 11; 1, 0, 1, 3]).ker = (⊥ : Submodule R _) := by
  simp [Submodule.eq_bot_iff, Fin.forall_fin_succ_pi]; grind

theorem ZadD4f_range [Field R] [CharZero R] :
    (Matrix.toLin' !![2, 0, 0, 1; -1, 1, -2, 2; 2, 1, -5, 11; 1, 0, 1, 3]).range = (⊤ : Submodule R _) := by
  simp [← Matrix.toLin_eq_toLin']; apply Matrix.range_toLin_eq_top
  simp [Matrix.det_succ_row_zero]; simp [Fin.sum_univ_succ, Fin.succAbove]; norm_num

theorem ZadD4g_ker [CommRing R] : (Matrix.toLin' !![1, 0, 0, 0; 0, 0, 0, 0; 2, 0, 0, 1; 1, 0, 0, 0]).ker
    = span R {![0, 1, 0, 0], ![0, 0, 1, 0]} := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, mem_span_pair]; grind

theorem ZadD4g_range [CommRing R] : (Matrix.toLin' !![1, 0, 0, 0; 0, 0, 0, 0; 2, 0, 0, 1; 1, 0, 0, 0]).range
    = span R {![1, 0, 0, 1], ![0, 0, 1, 0]} := by
  simp [Submodule.ext_iff, Fin.exists_fin_succ_pi, mem_span_pair, Fin.forall_fin_succ_pi]
  intro a b c rfl; use c - 2 * a; simp

theorem ZadD4h_ker [CommRing R] : (Matrix.toLin' !![1, 0, 0, 1; 0, 1, 1, 0; 1, 1, 1, 1; 1, 2, 2, 1]).ker
    = span R {![1, 0, 0, -1], ![0, 1, -1, 0]} := by
  simp [Submodule.ext_iff, Fin.forall_fin_succ_pi, mem_span_pair]; grind

theorem ZadD4h_range [CommSemiring R] : (Matrix.toLin' !![1, 0, 0, 1; 0, 1, 1, 0; 1, 1, 1, 1; 1, 2, 2, 1]).range
    = span R {![1, 0, 1, 1], ![0, 1, 1, 2]} := by
  simp [Submodule.ext_iff, Fin.exists_fin_succ_pi, mem_span_pair]; intro v; constructor
  · rintro ⟨x, y, z, t, rfl⟩; simp; ring_nf; tauto
  · rintro ⟨a, b, rfl⟩; use a, b, 0, 0; simp [mul_comm]
