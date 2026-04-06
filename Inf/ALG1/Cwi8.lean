import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Matrix.Reflection

open LinearMap

namespace ALG1

set_option linter.unusedVariables false in
theorem Zad8_1a : IsLinearMap ℝ fun ((x₁, x₂, x₃) : ℝ × ℝ × ℝ) => (x₁, x₂) :=
  isLinear ((fst _ _ _).prod (fst _ _ _ ∘ₗ snd _ _ _))

theorem Zad8_1b : ¬IsLinearMap ℝ fun ((x₁, x₂) : ℝ × ℝ) => x₁ * x₂ :=
  fun h => by simpa [self_eq_neg] using h.map_neg 1

theorem Zad8_1c : IsLinearMap ℝ fun ((x, y, z) : ℝ × ℝ × ℝ) => (2 * x - 2 * y, z - x, y - x) where
  map_add x y := by dsimp; ring_nf
  map_smul c x := by dsimp; ring_nf

theorem Zad8_1g [CommSemiring R] [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    IsLinearMap R fun X : Matrix n n R => X * A + A * X where
  map_add x y := by rw [add_mul, mul_add, add_assoc, add_left_comm (y * A), add_assoc]
  map_smul c x := by rw [smul_add, smul_mul_assoc, mul_smul_comm]

theorem Zad8_2a : (fun (x : Fin 3 → ℝ) => (2 * x 0 - x 1, 3 * x 0 + x 1 - x 2)) =
    Matrix.toLin (Pi.basisFun ℝ (Fin 3)) (Module.Basis.finTwoProd ℝ) !![2, -1, 0; 3, 1, -1] := by
  ext x
  · simp [Matrix.toLin_apply, Matrix.vecHead, Matrix.vecTail, sub_eq_add_neg]
  · simp [Matrix.toLin_apply, Matrix.vecHead, Matrix.vecTail, sub_eq_add_neg, add_assoc]

theorem Zad8_2b (α : ℝ) : (rotation (Real.Angle.toCircle α)).toMatrix
    Complex.basisOneI Complex.basisOneI = !![α.cos, -α.sin; α.sin, α.cos] := by
  rw [toMatrix_rotation]; simp

theorem Zad8_4 : ![5, -1, 0] ∈ !![1, 2, 3, 0; -1, 0, -1, 2; 2, -1, 1, 5].toLin'.range :=
  ⟨![1, 2, 0, 0], (Matrix.mulVecᵣ_eq _ _).symm⟩

theorem Zad8_D1a : IsLinearMap ℝ (starRingEnd ℂ) := Complex.conjAe.toLinearMap.isLinear

theorem Zad8_D2 [Semiring R] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
    (a : M₂) : IsLinearMap R (fun (_ : M₁) => a) ↔ a = 0 where
  mp h := h.map_zero
  mpr h := h ▸ isLinear 0
