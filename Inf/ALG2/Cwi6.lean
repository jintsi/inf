import Mathlib.Analysis.InnerProductSpace.GramMatrix

namespace ALG2.Cwi6

variable [DecidableEq n] [Fintype n] [CommRing α] [StarRing α] [RCLike K]

open Matrix Real

theorem Zad1 (hA : A ∈ unitaryGroup n α) (hB : B ∈ unitaryGroup n α) :
    A * B ∈ unitaryGroup n α := Submonoid.mul_mem _ hA hB

theorem Zad2 [CommRing R] [NoZeroDivisors R] [LinearOrder R] [Nontrivial R] [IsOrderedRing R]
    (hA : A ∈ orthogonalGroup n R) (hB : B ∈ orthogonalGroup n R) (h : A.det + B.det = 0) : (A + B).det = 0 := by
  suffices -A.det ^ 2 * (A + B).det = (A + B).det by
    rw [mul_left_eq_self₀] at this; apply this.resolve_left; apply ne_of_lt
    grw [← zero_lt_one, neg_nonpos, sq_nonneg]
  convert_to _ = (A * (A + B)ᵀ * B).det
  · rw [transpose_add, mul_add, add_mul, (mem_orthogonalGroup_iff n R).mp hA, one_mul, mul_assoc,
      (mem_orthogonalGroup_iff' n R).mp hB, mul_one, add_comm]
  simp [-transpose_add, ← add_eq_zero_iff_neg_eq.mp h]; ring

theorem Zad3 {A : Matrix n n K} (hA : A.IsHermitian) :
    spectrum K A ⊆ Set.range RCLike.ofReal := hA.spectrum_eq_image_range ▸ Set.image_subset_range _ _

theorem Zad4 {A : Matrix n n ℂ} (hA : A.IsHermitian) (hz : Complex.im z ≠ 0) :
    (A + scalar n z).Nondegenerate := by
  rw [nondegenerate_iff_det_ne_zero, add_comm, ← sub_neg_eq_add, ← eval_charpoly, Ne,
    ← Polynomial.IsRoot.def, ← mem_spectrum_iff_isRoot_charpoly]
  apply Set.subset_iff_notMem.mp (Zad3 hA.neg); simp_rw [Set.mem_range, not_exists, ← ne_eq]
  intro x; apply_fun Complex.im; simpa [eq_comm]

theorem Zad5 {A B : Matrix n n K} (hA : A.IsHermitian) :
    ∃ C D, Matrix.fromBlocks A B Bᴴ A = C * Matrix.diagonal D * C⁻¹ := by
  use ?C, ?D; convert (hA.fromBlocks rfl hA).spectral_theorem using 1
  rw [Unitary.conjStarAlgAut_apply]; congr; rfl; rfl; apply inv_eq_left_inv; simp

theorem Zad6 {A : Matrix n n K} (hA : A.IsHermitian) (h : IsNilpotent A) : A = 0 := by
  revert h; rw [hA.spectral_theorem, IsNilpotent]
  simpa [-Unitary.conjStarAlgAut_apply, ← map_pow, diagonal_pow] using fun k => eq_zero_of_pow_eq_zero

lemma _root_.Matrix.isHermitian_algebraMap (a : ℝ) : (algebraMap ℝ (Matrix n n K) a).IsHermitian := by
  simp [algebraMap_eq_diagonal, isHermitian_diagonal_iff, IsSelfAdjoint]

theorem _root_.Matrix.IsHermitian.spectrum_add_algebraMap {A : Matrix n n K} (hA : A.IsHermitian)
    (a : ℝ) : spectrum ℝ (A + algebraMap _ _ a) = (fun v => v + a) '' spectrum ℝ A := by
  have hA' := hA.add (isHermitian_algebraMap a)
  suffices spectrum K (A + algebraMap _ _ a) = (fun v => v + algebraMap _ _ a) '' spectrum K A by
    simp only [IsHermitian.spectrum_eq_image_range, ← IsHermitian.spectrum_real_eq_range_eigenvalues,
      hA, hA'] at this
    rw [← Set.image_eq_image RCLike.ofReal_injective (β := K), this]; simp [Set.ext_iff, -Set.image_add_right]
  simp [Set.ext_iff, Matrix.mem_spectrum_iff_isRoot_charpoly]
  simp [← sub_neg_eq_add, algebraMap_eq_diagonal, ← scalar_apply, ← map_neg, charpoly_sub_scalar]

open scoped ComplexOrder in
theorem Zad8 {A : Matrix n n K} (hA : A.IsHermitian) : ∃ a : ℝ, (A + algebraMap _ _ a).PosDef := by
  by_cases! IsEmpty n
  · use 0; simp [posDef_iff_dotProduct_mulVec, IsHermitian.ext_iff, funext_iff]
  use 1 - iInf hA.eigenvalues; rw [(hA.add (isHermitian_algebraMap _)).posDef_iff_eigenvalues_pos,
    ← Set.forall_mem_range, ← IsHermitian.spectrum_real_eq_range_eigenvalues]
  simp [-map_sub, hA.spectrum_add_algebraMap, hA.spectrum_real_eq_range_eigenvalues]; intro v i h
  suffices iInf hA.eigenvalues ≤ hA.eigenvalues i by linarith
  apply ciInf_le; simp

omit [DecidableEq n] in
theorem Zad9 {A B : Matrix n n K} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace = (A * B).trace := by
  simp [← RCLike.conj_eq_iff_re, ← RCLike.star_def, ← trace_conjTranspose, hA.eq, hB.eq]
  apply trace_mul_comm

theorem Zad11 : A ∈ orthogonalGroup (Fin 2) ℝ ↔ ∃ θ,
    A = !![cos θ, sin θ; -sin θ, cos θ] ∨ A = !![cos θ, sin θ; sin θ, -cos θ] where
  mp hA := by
    simp [mem_orthogonalGroup_iff, ← Matrix.ext_iff, mul_apply] at hA; rcases hA with ⟨⟨h₀, h₁⟩, -, h₂⟩
    use Complex.arg ⟨A 0 0, A 0 1⟩; rw [Complex.cos_arg, Complex.sin_arg]; swap
    · rw [← norm_ne_zero_iff, Complex.norm_eq_sqrt_sq_add_sq]; simp [sq, h₀]
    simp [Complex.norm_eq_sqrt_sq_add_sq, sq, h₀, ← Matrix.ext_iff]; grind
  mpr h := by rcases h with ⟨θ, rfl | rfl⟩ <;>
    simp [mem_orthogonalGroup_iff, vecHead, vecTail, ← Matrix.ext_iff, ← sq, mul_comm]

theorem Zad12 : !![(1 : ℝ), 0, 0; 0, 2, 2; 0, 2, 2].PosSemidef := by
  simp [posSemidef_iff_dotProduct_mulVec]; and_intros
  · simp [IsSymm.ext_iff]; intro i j; fin_cases i <;> fin_cases j <;> rfl
  simp [Fin.forall_fin_succ_pi]; intro x y z
  convert_to 0 ≤ x ^ 2 + 2 * (y + z) ^ 2 using 1
  · rfl
  · ring
  · positivity

theorem ZadD1 [Nonempty n] (hA : A ∈ orthogonalGroup n K) (hB : B ∈ orthogonalGroup n K) :
    A ^ 2 - B ^ 2 ≠ A * B := by
  apply_fun (Aᵀ * · * Bᵀ)
  simp_rw [sq, mul_sub, sub_mul, ← mul_assoc, (mem_orthogonalGroup_iff' n K).mp hA, one_mul,
    mul_assoc, (mem_orthogonalGroup_iff n K).mp hB, mul_one]
  apply_fun trace; simp [trace, mul_apply]; rw [Finset.sum_comm]; simp; norm_cast; simp [eq_comm]

alias ZadD3 := posDef_gram_of_linearIndependent
