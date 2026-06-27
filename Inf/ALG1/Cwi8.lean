import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Matrix.Reflection

open LinearMap

namespace ALG1.Cwi8

set_option linter.unusedVariables false in
theorem Zad1a : IsLinearMap ℝ fun ((x₁, x₂, x₃) : ℝ × ℝ × ℝ) => (x₁, x₂) :=
  isLinear ((fst _ _ _).prod (fst _ _ _ ∘ₗ snd _ _ _))

theorem Zad1b : ¬IsLinearMap ℝ fun ((x₁, x₂) : ℝ × ℝ) => x₁ * x₂ :=
  fun h => by simpa [self_eq_neg] using h.map_neg 1

theorem Zad1c : IsLinearMap ℝ fun ((x, y, z) : ℝ × ℝ × ℝ) => (2 * x - 2 * y, z - x, y - x) where
  map_add x y := by dsimp; ring_nf
  map_smul c x := by dsimp; ring_nf

open Polynomial in
theorem Zad1d : IsLinearMap ℝ fun (p : ℝ[X]) => derivative^[2] ((X ^ 2 - X - 1) * p) where
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

theorem Zad4 : ![5, -1, 0] ∈ !![1, 2, 3, 0; -1, 0, -1, 2; 2, -1, 1, 5].toLin'.range :=
  ⟨![1, 2, 0, 0], (Matrix.mulVecᵣ_eq _ _).symm⟩

theorem ZadD1a : IsLinearMap ℝ (starRingEnd ℂ) := Complex.conjAe.toLinearMap.isLinear

theorem ZadD1b : ¬IsLinearMap ℂ (starRingEnd ℂ) :=
  fun h => by simpa [neg_eq_self] using h.map_smul Complex.I 1

theorem ZadD2 [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
    (a : M₂) : IsLinearMap R (fun (_ : M₁) => a) ↔ a = 0 where
  mp h := h.map_zero
  mpr h := h ▸ isLinear 0

alias ZadD3 := IsLinearMap.map_zero
