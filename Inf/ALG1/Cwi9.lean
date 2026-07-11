import Mathlib.RingTheory.Polynomial.DegreeLT

theorem add_one_smul [Semiring R] [AddCommMonoid M] [Module R M] (r : R) (x : M) :
    (r + 1) • x = r • x + x := by rw [add_smul, one_smul]

@[simp]
theorem Ring.inverse_neg [Ring R] (a : R) : inverse (-a) = -inverse a := by
  rw [← neg_one_mul, inverse_mul, eq_comm, ← mul_neg_one, eq_mul_inverse_iff_mul_eq] <;> simp

@[simp]
theorem Matrix.transpose_fin_two_of :
    transpose !![a, b; c, d] = !![a, c; b, d] := by
  ext i j; fin_cases i <;> fin_cases j <;> dsimp

@[simp]
theorem Matrix.transpose_fin_three_of :
    transpose !![a, b, c; d, e, f; g, h, i] = !![a, d, g; b, e, h; c, f, i] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

attribute [simp] Module.Basis.coePiBasisFun.toMatrix_eq_transpose

/-- Construct a basis from basis vectors that form a nondegenerate matrix in a different basis
(typically `Pi.basisFun`). -/
noncomputable def Module.Basis.ofDetNeZero [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R M) (v : ι → M) (hv : IsUnit (b.toMatrix v).det) :
    Basis ι R M := b.map ((b.toMatrix v).toLinearEquiv b hv)

@[simp]
theorem Module.Basis.toFun_ofDetNeZero [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R M) (v : ι → M) (hv : IsUnit (b.toMatrix v).det) :
    b.ofDetNeZero v hv = v := by ext i; simp [ofDetNeZero]

theorem Module.Basis.ofDetNeZero_toMatrix [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R M) (v : ι → M) (hv : IsUnit (b.toMatrix v).det)
    (v' : ι' → M) : (b.ofDetNeZero v hv).toMatrix v' = (b.toMatrix v)⁻¹ * b.toMatrix v' := by
  ext i j; simp [ofDetNeZero, toMatrix_apply, Matrix.toLinearEquiv, ← LinearMap.toMatrix_symm,
    LinearMap.toMatrix, Finsupp.single_eq_pi_single, Matrix.mulVec_apply, Matrix.mul_apply']
  rfl

namespace ALG1.Cwi9

open Module Basis

theorem Zad1a [Field K] [CharZero K] (v : Fin 3 → K)
    (hv : ((Pi.basisFun K (Fin 3)).ofDetNeZero ![![1, 0, 1], ![0, 2, 1], ![0, 0, 1]]
      (by simp [Matrix.det_fin_three])).equivFun v = ![1, 0, 2]) :
    ((Pi.basisFun K (Fin 3)).ofDetNeZero ![![1, 1, 0], ![0, 1, 0], ![0, 0, 1]]
      (by simp [Matrix.det_fin_three])).equivFun v = ![1, -1, 3] := by
  rw [← LinearEquiv.eq_symm_apply] at ⊢ hv; subst hv
  simp [Fin.sum_univ_three]; norm_num

theorem Zad1b [Field K] [CharZero K] [AddCommGroup V] [Module K V] (B : Basis (Fin 3) K V) :
    (B.ofDetNeZero ![B 0 + B 1, B 1 + B 2, B 0 + B 2] (by
      simp [Matrix.det_fin_three, B.toMatrix_apply])).equivFun
    (B.equivFun.symm ![1, 2, 3]) = ![0, 2, 1] := by
  rw [← LinearEquiv.eq_symm_apply]; simp [Fin.sum_univ_three]
  abel_nf; norm_num [← add_one_smul]

theorem Zad1c [CommRing R] [AddCommGroup M] [Module R M] (B : Basis (Fin 4) R M) :
    (B.ofDetNeZero ![B 0, 2 • B 0 + B 1, B 0 + B 2, 2 • B 0 + B 3] (by
      simp [Matrix.det_succ_column_zero, B.toMatrix_apply, Fin.sum_univ_succ])).equivFun
    (B.equivFun.symm ![1, 2, 3, 4]) = ![-14, 2, 3, 4] := by
  rw [← LinearEquiv.eq_symm_apply]; simp [Fin.sum_univ_four]
  apply B.repr.injective; ext i; simp; fin_cases i <;> simp; norm_num

noncomputable abbrev Zad2a.B [CommRing R] :=
  (Pi.basisFun R (Fin 2)).ofDetNeZero !![3, 1; 2, 1] (by norm_num [Matrix.det_fin_two])

noncomputable abbrev Zad2a.C [Field K] [CharZero K] :=
  (Pi.basisFun K (Fin 2)).ofDetNeZero !![1, -1; 2, 3] (by norm_num [Matrix.det_fin_two])

theorem Zad2a.B_to_C [Field K] [CharZero K] :
    C.toMatrix (B (R := K)) = (5⁻¹ : K) • !![7, 4; 4, 3] := by
  rw [ofDetNeZero_toMatrix]; norm_num [-Matrix.cons_transpose, Matrix.inv_def]

theorem Zad2a.C_to_B [Field K] [CharZero K] : B.toMatrix (C (K := K)) = !![3, -4; -4, 7] := by
  rw [ofDetNeZero_toMatrix]; norm_num [-Matrix.cons_transpose, Matrix.inv_def]

noncomputable abbrev Zad2b.B [Field K] [CharZero K] :=
  (Pi.basisFun K (Fin 3)).ofDetNeZero !![1, 1, 0; 0, 1, 1; 1, 0, 1] (by simp [Matrix.det_fin_three])

noncomputable abbrev Zad2b.C [Field K] [CharZero K] :=
  (Pi.basisFun K (Fin 3)).ofDetNeZero !![2, 1, 1; 1, 2, 1; 1, 1, 2]
    (by simp [Matrix.det_fin_three]; norm_num)

theorem Zad2b.B_to_C [Field K] [CharZero K] :
    C.toMatrix (B (K := K)) = (2⁻¹ : K) • !![1, -1, 1; 1, 1, -1; -1, 1, 1] := by
  rw [ofDetNeZero_toMatrix]
  simp [-Matrix.cons_transpose, Matrix.inv_def, Matrix.det_fin_three]; norm_num

theorem Zad2b.C_to_B [Field K] [CharZero K] :
    B.toMatrix (C (K := K)) = !![1, 1, 0; 0, 1, 1; 1, 0, 1] := by
  rw [ofDetNeZero_toMatrix]
  simp [-Matrix.cons_transpose, Matrix.inv_def, Matrix.det_fin_three]; norm_num

noncomputable abbrev Zad2c.C [Field K] [CharZero K] :=
  (Pi.basisFun K (Fin 3)).ofDetNeZero !![3, 3, 4; -1, 2, 2; 1, 1, 1]
    (by simp [Matrix.det_fin_three]; norm_num)

theorem Zad2c.B_to_C [Field K] [CharZero K] :
    C.toMatrix (Pi.basisFun K (Fin 3)) = (3⁻¹ : K) • !![0, -3, 3; -1, 1, 0; 2, 10, -9] := by
  rw [ofDetNeZero_toMatrix]
  simp [-Matrix.cons_transpose, Matrix.inv_def, Matrix.det_fin_three]; norm_num

theorem Zad2c.C_to_B [Field K] [CharZero K] :
    (Pi.basisFun K (Fin 3)).toMatrix (C (K := K)) = !![3, -1, 1; 3, 2, 1; 4, 2, 1] := by
  simp [-Matrix.cons_transpose]

abbrev Zad3a.F [Semiring R] : R × R →ₗ[R] R × R where
  toFun xy := (2 * xy.1 + xy.2, xy.2)
  map_add' x y := by simp [two_mul]; ac_nf
  map_smul' c x := by simp [two_mul, mul_add]

noncomputable abbrev Zad3a.B [Field K] [CharZero K] :=
  (Basis.finTwoProd K).ofDetNeZero ![(1, 3), (0, 2)] (by simp [Matrix.det_fin_two, toMatrix_apply])

noncomputable abbrev Zad3a.C [Field K] [CharZero K] :=
  (Basis.finTwoProd K).ofDetNeZero ![(2, 2), (3, 1)]
    (by simp [Matrix.det_fin_two, toMatrix_apply]; norm_num)

open Zad3a in
theorem Zad3a [Field K] [CharZero K] : LinearMap.toMatrix (R := K) B C F = !![1, 1; 1, 0] := by
  rw [LinearMap.toMatrix_eq_basisToMatrix, ofDetNeZero_toMatrix]
  simp [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two, toMatrix_apply]
  and_intros <;> (ext i; fin_cases i) <;> norm_num [Matrix.vecMul_apply_eq_sum, toMatrix_apply]

abbrev Zad3b.F [Ring R] : R × R →ₗ[R] Fin 3 → R where
  toFun xy := ![xy.1 + xy.2, xy.1 - xy.2, xy.2]
  map_add' x y := by simp; abel_nf; trivial
  map_smul' c x := by simp [mul_add, mul_sub]

noncomputable abbrev Zad3b.B [Field K] [CharZero K] :=
  (Basis.finTwoProd K).ofDetNeZero ![(1, -3), (2, 0)]
    (by simp [Matrix.det_fin_two, toMatrix_apply])

noncomputable abbrev Zad3b.C [CommRing R] :=
  (Pi.basisFun R (Fin 3)).ofDetNeZero !![1, 1, 0; 0, 0, 1; 1, 0, 1] (by simp [Matrix.det_fin_three])

open Zad3b in
theorem Zad3b [Field K] [CharZero K] :
    LinearMap.toMatrix (R := K) B C F = !![4, 2; 3, 0; -6, 0] := by
  rw [LinearMap.toMatrix_eq_basisToMatrix, ofDetNeZero_toMatrix]
  simp [-Matrix.cons_transpose, Matrix.inv_def, Matrix.det_fin_three]
  and_intros <;> (ext i; fin_cases i) <;>
    simp [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_three, toMatrix_apply] <;> norm_num

abbrev Zad3c.F [Ring R] : (Fin 3 → R) →ₗ[R] R × R where
  toFun xyz := (xyz 0 - xyz 1, xyz 1 - xyz 2)
  map_add' x y := by simp; abel_nf; trivial
  map_smul' c x := by simp [mul_sub]

noncomputable abbrev Zad3c.B [CommRing R] :=
  (Pi.basisFun R (Fin 3)).ofDetNeZero !![1, 2, 2; 1, 1, 1; 1, 1, 2]
    (by simp [Matrix.det_fin_three]; norm_num)

noncomputable abbrev Zad3c.C [CommRing R] :=
  (Basis.finTwoProd R).ofDetNeZero ![(1, 1), (1, 0)] (by simp [Matrix.det_fin_two, toMatrix_apply])

open Zad3c in
theorem Zad3c [CommRing R] :
    LinearMap.toMatrix (R := R) B C F = !![0, 0, -1; -1, 0, 1] := by
  rw [LinearMap.toMatrix_eq_basisToMatrix, ofDetNeZero_toMatrix]
  simp [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two, toMatrix_apply]
  and_intros <;> (ext i; fin_cases i) <;>
    simp [Matrix.vecMul_apply_eq_sum, toMatrix_apply] <;> norm_num

open Polynomial

noncomputable def Zad5.F [CommSemiring R] : R[X]_4 →ₗ[R] R[X]_4 :=
  Matrix.toLin (degreeLT.basis R 4) (degreeLT.basis R 4) (Matrix.diagonal ![1, 1, 1, 0])

theorem Zad5.F_apply [CommSemiring R] {p : R[X]_4} : F (R := R) p = p.val.erase 3 := by
  ext i; rw [← (degreeLT.basis R 4).sum_repr p]
  simp [F, Fin.sum_univ_four, coeff_erase, coeff_one, coeff_X]
  split_ifs <;> first | omega | simp

noncomputable def Zad5.G [Field K] [CharZero K] : K[X]_4 →ₗ[K] K[X]_4 :=
  (degreeLT.basis K 4).map (!![0, 0, 1, 1; 0, 1, 0, 1; 1, 0, 0, 1; 1, 1, 1, 1].toLinearEquiv
    (degreeLT.basis K 4) (by simp [Matrix.det_succ_row_zero, Fin.sum_univ_four,
      Fin.sum_univ_three, Fin.succAbove]; norm_num))
  |>.constr K ![⟨X ^ 3 + X, by rw [mem_degreeLT]; compute_degree!⟩,
                ⟨X ^ 3 + 1, by rw [mem_degreeLT]; compute_degree!⟩,
                ⟨X ^ 3 + X ^ 2 + X + 1, by rw [mem_degreeLT]; compute_degree!⟩, 0]

theorem Zad5.G_values [Field K] [CharZero K] :
    (G (K := K) ⟨X ^ 3 + X ^ 2, by rw [mem_degreeLT]; compute_degree!⟩).val = X ^ 3 + X ∧
    (G (K := K) ⟨X ^ 3 + X, by rw [mem_degreeLT]; compute_degree!⟩).val = X ^ 3 + 1 ∧
    (G (K := K) ⟨X ^ 3 + 1, by rw [mem_degreeLT]; compute_degree!⟩).val = X ^ 3 + X ^ 2 + X + 1 ∧
    (G (K := K) ⟨X ^ 3 + X ^ 2 + X + 1, by rw [mem_degreeLT]; compute_degree!⟩).val = 0 := by
  rw [G]; and_intros; map_tacs [
    convert congrArg Subtype.val (constr_basis (M' := K[X]_4) _ _ _ (0 : Fin 4));
    convert congrArg Subtype.val (constr_basis (M' := K[X]_4) _ _ _ (1 : Fin 4));
    convert congrArg Subtype.val (constr_basis (M' := K[X]_4) _ _ _ (2 : Fin 4));
    convert congrArg Subtype.val (constr_basis (M' := K[X]_4) _ _ _ (3 : Fin 4))
  ]
  all_goals simp [Fin.sum_univ_four] <;> ac_nf

theorem Zad5.toMatrix_G [Field K] [CharZero K] :
    LinearMap.toMatrix (degreeLT.basis K 4) (degreeLT.basis K 4) G =
    (2⁻¹ : K) • !![0, 0, -2, 2; 0, -2, 0, 2; 1, -1, -1, 1; -1, -1, -1, 3] := by
  have : !![(0 : K), 0, 1, 1; 0, 1, 0, 1; 1, 0, 0, 1; 1, 1, 1, 1].det = 2 := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_four, Fin.sum_univ_three, Fin.succAbove]; norm_num
  ext i j; simp [LinearMap.toMatrix_apply, G, Matrix.toLinearEquiv, Matrix.inv_def,
    Matrix.adjugate_fin_succ_eq_det_submatrix, this, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_three, Fin.succAbove]
    <;> norm_num [coeff_one, coeff_X]

theorem Zad5.toMatrix_F_comp_G [Field K] [CharZero K] :
    LinearMap.toMatrix (degreeLT.basis K 4) (degreeLT.basis K 4) (F ∘ₗ G) =
    (2⁻¹ : K) • !![0, 0, -2, 2; 0, -2, 0, 2; 1, -1, -1, 1; 0, 0, 0, 0] := by
  simp [LinearMap.toMatrix_comp (degreeLT.basis K 4) (degreeLT.basis K 4), F, toMatrix_G]
  ext i j; fin_cases i <;> simp; fin_cases j <;> rfl

theorem Zad5.toMatrix_G_comp_F [Field K] [CharZero K] :
    LinearMap.toMatrix (degreeLT.basis K 4) (degreeLT.basis K 4) (G ∘ₗ F) =
    (2⁻¹ : K) • !![0, 0, -2, 0; 0, -2, 0, 0; 1, -1, -1, 0; -1, -1, -1, 0] := by
  simp [LinearMap.toMatrix_comp (degreeLT.basis K 4) (degreeLT.basis K 4), F, toMatrix_G]
  simp [funext_iff, Matrix.vecMul_diagonal, Fin.forall_fin_succ]

theorem ZadD1 [DivisionRing K] (f : (Fin 3 → K) →ₗ[K] Fin 5 → K)
    (h : f.range = Submodule.span K {![1, 0, 1, -1, 0], ![0, 1, 0, 1, 0], ![1, 1, 1, 1, 1]})
    : (⇑f).Injective := by
  suffices finrank K f.range = finrank K (Fin 3 → K) by
    rw [← f.finrank_range_add_finrank_ker] at this; simpa [f.ker_eq_bot] using this
  rw [h]; simp
  convert finrank_span_eq_card (R := K) (b := ![![(1 : K), 0, 1, -1, 0], ![0, 1, 0, 1, 0], ![1, 1, 1, 1, 1]]) ?_
  all_goals try (ext; simp; tauto)
  · simp
  · simp [linearIndependent_finSucc, Submodule.mem_span_singleton, Submodule.mem_span_pair]

theorem ZadD2 {M : Type u} [Ring R] [AddCommGroup M] [Module R M] [HasRankNullity.{u} R]
    [StrongRankCondition R] [IsDomain R] [IsTorsionFree R M] [Module.Finite R M] {f : M →ₗ[R] M}
    (h : finrank R f.range = finrank R (f ^ 2).range) : Disjoint f.ker f.range := by
  symm; apply Submodule.disjoint_ker_of_finrank_le; apply le_of_eq; rw [h]
  congr!; all_goals (ext x; simp [sq])

theorem ZadD9 [DivisionRing K] {f : (Fin 4 → K) →ₗ[K] Fin 3 → K}
    (h : f.ker = K ∙ ![1, -1, 0, 1]) : (⇑f).Surjective := by
  rw [← f.range_eq_top]; apply Submodule.eq_top_of_finrank_eq
  rw [← add_left_inj, f.finrank_range_add_finrank_ker, h, finrank_fin_fun, finrank_fin_fun,
    finrank_span_singleton]; simp
