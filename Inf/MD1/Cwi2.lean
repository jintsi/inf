import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Nat.Choose.Vandermonde

--TODO: rooks

--TODO: Zad3

theorem composition_length_card (n k : ℕ) [NeZero n] :
    Finset.card {c : Composition n | c.length = k + 1} = (n - 1).choose k :=
  calc Finset.card {c : Composition n | c.length = k + 1}
  _ = Finset.card {c : CompositionAsSet n | c.length = k + 1} :=
    Finset.card_equiv (compositionEquiv n) fun c => by simp [compositionEquiv]
  _ = Finset.card {s : Finset (Fin (n - 1)) | s.card = k} :=
    (Finset.card_equiv (compositionAsSetEquiv n).symm fun s => by
      simp [compositionAsSetEquiv, CompositionAsSet.length, ← Finset.filter_union_right]
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
        <;> simp [Finset.filter_eq', add_comm 1, NeZero.ne]
      · apply Eq.congr_left
        apply Finset.card_nbij (fun i => (i.castSucc.cast (Nat.sub_one_add_one (NeZero.ne n))).succ)
          <;> simp [Set.MapsTo, Set.SurjOn, Set.subset_def]
        · exact fun x hx => ⟨x, hx, rfl⟩
        · intro x y hy hx; exists y, hy; rw [← Fin.val_inj]; simp [hx.symm]
      · intro x hx; grind
    ).symm
  _ = (n - 1).choose k := by simp

theorem FinVec.composition_pos_card (n k : ℕ) [NeZero n] [NeZero k] :
    {x : Fin k → ℕ | (∀ i, 0 < x i) ∧ FinVec.sum x = n}.ncard = (n - 1).choose (k - 1) :=
  calc {x : Fin k → ℕ | (∀ i, 0 < x i) ∧ FinVec.sum x = n}.ncard
  _ = {c : Composition n | c.length = k}.ncard := by
    apply Set.ncard_congr fun x hx => {
      blocks := List.ofFn x, blocks_pos := by simp [hx.left]
      blocks_sum := by simp_all [List.sum_ofFn]} <;> simp [Composition.length, Composition.ext_iff]
    intro c hc; use fun i => c.blocksFun (i.cast hc.symm)
    simp [Composition.blocksFun, -List.get_eq_getElem, Fin.sum_congr']; constructor; simp
    conv => rhs; rw [← Composition.ofFn_blocksFun]
    rw [List.ofFn_inj', Fin.sigma_eq_iff_eq_comp_cast]; use hc.symm
    ext x; simp [Composition.blocksFun]
  _ = Finset.card {c : Composition n | c.length = k} := by convert Set.ncard_coe_finset _; simp
  _ = (n - 1).choose (k - 1) := by
    convert composition_length_card n (k - 1); exact (Nat.sub_add_cancel NeZero.one_le).symm

theorem FinVec.composition_card (n k : ℕ) [NeZero k] :
    {x : Fin k → ℕ | FinVec.sum x = n}.ncard = (n + k - 1).choose (k - 1) :=
  calc {x : Fin k → ℕ | FinVec.sum x = n}.ncard
  _ = {x : Fin k → ℕ | (∀ i, 0 < x i) ∧ FinVec.sum x = n + k}.ncard := by
    apply Set.BijOn.ncard_eq (f := fun x i => x i + 1)
    simp [Set.BijOn, Set.MapsTo, ← Finset.sum_add_card_nsmul, Set.InjOn, funext_iff,
      Set.SurjOn, Set.subset_def]; intro x hpos hsum; use fun i => x i - 1; and_intros
    · conv at hsum => lhs; rhs; ext i; rw [← Nat.sub_add_cancel (hpos i)]
      rw [← Finset.sum_add_card_nsmul] at hsum; simp_all
    · simp; exact fun i => Nat.sub_add_cancel (hpos i)
  _ = (n + k - 1).choose (k - 1) := FinVec.composition_pos_card (n + k) k

namespace MD1.Cwi2

theorem Zad4i : {(x₁, x₂, x₃, x₄) : ℕ × ℕ × ℕ × ℕ | x₁ + x₂ + x₃ + x₄ = 7}.ncard = 120 :=
  calc {(x₁, x₂, x₃, x₄) : ℕ × ℕ × ℕ × ℕ | x₁ + x₂ + x₃ + x₄ = 7}.ncard
  _ = {x : Fin 4 → ℕ | FinVec.sum x = 7}.ncard := by
    apply Set.BijOn.ncard_eq (f := fun ⟨x, y, z, w⟩ => ![x, y, z, w])
    simp [Set.BijOn, Set.MapsTo, FinVec.sum, Set.SurjOn, Set.subset_def]
    exact fun x hx => ⟨x 0, x 1, x 2, x 3, hx, FinVec.etaExpand_eq x⟩
  _ = Nat.choose 10 3 := FinVec.composition_card _ _

theorem Zad4ii : {(x₁, x₂, x₃, x₄) : ℕ × ℕ × ℕ × ℕ | 0 < x₁ ∧ 0 < x₂ ∧ 0 < x₃ ∧ 0 < x₄
    ∧ x₁ + x₂ + x₃ + x₄ = 7}.ncard = 20 :=
  calc {(x₁, x₂, x₃, x₄) : ℕ × ℕ × ℕ × ℕ | _}.ncard
  _ = {x : Fin 4 → ℕ | (∀ i, 0 < x i) ∧ FinVec.sum x = 7}.ncard := by
    apply Set.BijOn.ncard_eq (f := fun ⟨x, y, z, w⟩ => ![x, y, z, w])
    simp [Set.BijOn, Set.MapsTo, Fin.forall_fin_succ, FinVec.sum, Set.SurjOn, Set.subset_def]
    and_intros; tauto
    intro x _ _ _ _ _; use x 0, x 1, x 2, x 3; simp [*]; exact FinVec.etaExpand_eq x
  _ = Nat.choose 6 3 := FinVec.composition_pos_card _ _

theorem Zad6 (n k : ℕ) : ∑ j ∈ Finset.range n, j.choose k = n.choose (k + 1) := by
  cases n; simp; rename_i n
  rw [← Nat.sum_Icc_choose]; apply Finset.sum_congr_of_eq_on_inter <;> grind

theorem Zad7 (n k : ℕ) : ∑ j ∈ Finset.range (k + 1), (n + j).choose j = (n + k + 1).choose k := by
  convert Nat.sum_range_add_choose k n using 1
  · congr; funext j; rw [add_comm, Nat.choose_symm_add]
  · rw [add_comm n]; exact Nat.choose_symm_of_eq_add (add_assoc _ _ _)

theorem Zad8 (n : ℕ) : Finset.card {f : Fin n → Fin n | Monotone f} = (2 * n - 1).choose n :=
  calc Finset.card {f : Fin n → Fin n | Monotone f}
  _ = Finset.card {f : Fin n → Fin (2 * n - 1) | StrictMono f} := by
    apply Finset.card_nbij (fun f i => ((f i).addNat i).castLE (by lia))
      <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def, funext_iff]
    · simp [Monotone, StrictMono, ← Fin.val_fin_lt, ← Fin.val_fin_le]
      exact fun f hf a b h => add_lt_add_of_le_of_lt (hf h.le) h
    · cases n; · simp [Monotone]
      intro f hf; exists fun i => ⟨f i - i, ?_⟩; swap; simp [Fin.ext_iff]; and_intros
      · simp [Fin.monotone_iff_le_succ]; intro i; grind [hf i.castSucc_lt_succ]
      · intro i; apply Nat.sub_add_cancel; induction i using Fin.induction; · simp
        rename_i i ih; simp at *; grw [ih]; exact hf i.castSucc_lt_succ
      · rename_i n; induction i using Fin.reverseInduction; · grind
        rename_i i ih; simp at *; grw [← Nat.lt_add_one_iff, add_assoc, ← ih]
        exact hf i.castSucc_lt_succ
  _ = ((Finset.univ : Finset (Fin (2 * n - 1))).powersetCard n).card := by
    apply Finset.card_bij (fun f h => Finset.univ.map ⟨f, StrictMono.injective (by simp_all)⟩)
      <;> simp [← Finset.coe_inj]
    · exact fun f hf g hg => (hf.range_inj hg).mp
    · intro s h; exists s.orderEmbOfFin h; simp [StrictMono]
  _ = (2 * n - 1).choose n := by simp

--  TODO: Zad9

theorem Zad10 (n k : ℕ) : ∑ i ≤ k, n.choose i * (n - i).choose (k - i) = 2 ^ k * n.choose k := by
  let F : Finset (Finset (Fin n) × Finset (Fin n)) := {(s, t) : _ | s.card = k ∧ t ⊆ s}
  have h1 := calc F.card
    _ = ∑ s ∈ .powersetCard k .univ, {st ∈ F | st.1 = s}.card :=
      Finset.card_eq_sum_card_fiberwise (by simp [Set.MapsTo, F]; tauto)
    _ = ∑ s ∈ .powersetCard k (.univ : Finset (Fin n)), s.powerset.card := by
      apply Finset.sum_congr rfl; intro s hs; simp at hs; apply Finset.card_nbij Prod.snd <;>
        simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def] <;> grind
    _ = ∑ s ∈ .powersetCard k (.univ : Finset (Fin n)), 2 ^ k := by
      congr! with s hs; simp_all
    _ = 2 ^ k * n.choose k := by simp [mul_comm]
  have h2 := calc F.card
    _ = ∑ i ≤ k, {st ∈ F | st.2.card = i}.card := Finset.card_eq_sum_card_fiberwise
      (by simp [Set.MapsTo, F]; intro s t hs ht; exact hs ▸ Finset.card_le_card ht)
    _ = ∑ i ≤ k, ∑ t ∈ .powersetCard i .univ, {st ∈ F | st.2 = t}.card := by
      congr! with i hi; rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd)]
      · congr! 2 with t ht; simp [Finset.filter_filter] at *; congr; grind
      · simp [Set.MapsTo]
    _ = ∑ i ≤ k, ∑ t ∈ .powersetCard i .univ, Finset.card {s : _ | s.card = k - i ∧ Disjoint t s} := by
      congr! with i hi t ht; apply Finset.card_nbij fun st => st.1 \ t <;> try first | infer_instance |
        simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def, Finset.disjoint_sdiff, F]
      · intro s t hs h ht; simp_all [Finset.card_sdiff_of_subset]
      · intro s t' hs ht' h' s' t hs' ht'' h'' h; subst h' h''; simp; apply_fun (· ∪ t) at h
        simp [Finset.sdiff_union_of_subset ht', Finset.sdiff_union_of_subset ht''] at h; assumption
      · intro s hs hd; exists t ∪ s; simp_all [Finset.union_sdiff_cancel_left]
    _ = ∑ i ≤ k, ∑ t ∈ .powersetCard i .univ, ((Finset.univ \ t).powersetCard (k - i)).card := by
      congr!; ext s; simp [Finset.disjoint_right, Finset.subset_iff]; tauto
    _ = ∑ i ≤ k, n.choose i * (n - i).choose (k - i) := by
      congr! with i hi; convert Finset.sum_const_nat ?_ <;> simp
      intro t ht; simp [Finset.card_univ_diff, ht]
  simp_all

theorem Zad11a (n : ℕ) : ∑ k ≤ n, k * n.choose k = n * 2 ^ (n - 1) := by
  apply and_self_iff.mp; and_intros
  · let F : Finset (Finset (Fin n) × Fin n) := {(s, x) : _ | x ∈ s}
    have h1 := calc F.card
      _ = ∑ s, {sx ∈ F | sx.1 = s}.card :=
        Finset.card_eq_sum_card_fiberwise (by simp [Set.MapsTo])
      _ = ∑ s : Finset (Fin n), s.card := by
        congr with s; apply Finset.card_nbij Prod.snd
          <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def, F] <;> grind only
      _ = ∑ k ≤ n, n.choose k * k := by
        convert Finset.sum_powerset_apply_card id using 2 with _ _ k hk
          <;> simp [Nat.range_succ_eq_Iic]
      _ = ∑ k ≤ n, k * n.choose k := by congr! 1; ring
    have h2 := calc F.card
      _ = ∑ x : Fin n, (Finset.univ \ {x}).powerset.card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd)]
        · congr; ext x; apply Finset.card_nbij (compl ∘ Prod.fst)
            <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def] <;> try grind
          intro s h; exists sᶜ; simpa [F]
        · simp [Set.mapsTo_univ]
      _ = n * 2 ^ (n - 1) := by convert Finset.sum_const_nat ?_ <;> simp [Finset.card_univ_diff]
    simp_all
  · rw [← Nat.sum_range_mul_choose]; congr; ext; simp

theorem Zad11b {n : ℕ} (hn : 1 < n) : ∑ k ≤ n, k ^ 2 * n.choose k = (n + n ^ 2) * 2 ^ (n - 2) := by
  apply and_self_iff.mp; and_intros
  · let F : Finset (Finset (Fin n) × Fin n × Fin n) := {(s, x, y) : _ | x ∈ s ∧ y ∈ s}
    have h1 := calc F.card
      _ = ∑ s, {sxy ∈ F | sxy.1 = s}.card :=
        Finset.card_eq_sum_card_fiberwise (by simp [Set.MapsTo])
      _ = ∑ s : Finset (Fin n), (s ×ˢ s).card := by
        congr with s; apply Finset.card_nbij Prod.snd
          <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def, F] <;> grind only
      _ = ∑ k ≤ n, n.choose k * k ^ 2 := by
        convert Finset.sum_powerset_apply_card (· ^ 2) using 2 with _ _ k hk
          <;> simp [sq, Nat.range_succ_eq_Iic]
      _ = ∑ k ≤ n, k ^ 2 * n.choose k := by grind
    have h2 := calc F.card
      _ = ∑ xy : Fin n × Fin n, (Finset.univ \ {xy.1, xy.2}).powerset.card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd)]
        · congr; ext x; apply Finset.card_nbij (compl ∘ Prod.fst)
            <;> simp [Set.MapsTo, Set.InjOn, Set.SurjOn, Set.subset_def] <;> try grind
          intro s h; exists sᶜ; simp [F]; grind
        · simp [Set.mapsTo_univ]
      _ = ∑ xy : Fin n × Fin n with xy.1 = xy.2, (Finset.univ \ {xy.1, xy.2}).powerset.card +
          ∑ xy : Fin n × Fin n with xy.1 ≠ xy.2, (Finset.univ \ {xy.1, xy.2}).powerset.card :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ = n * 2 ^ (n - 1) + (n * n - n) * 2 ^ (n - 2) := by
        have : Finset.card {xy : Fin n × Fin n | xy.1 = xy.2} = n := by
          apply Finset.card_eq_of_bijective fun i h => (⟨i, h⟩, ⟨i, h⟩) <;> simp [← Fin.val_inj]
        congr <;> convert Finset.sum_const_nat ?_ <;>
          simp [this, Finset.filter_not, Finset.card_univ_diff]; intro a b h; simp [h]
      _ = 2 * n * 2 ^ (n - 2) + (n ^ 2 - n) * 2 ^ (n - 2) := by
        conv => rhs; lhs; rw [mul_comm 2, mul_assoc, show n - 2 = n - 1 - 1 by lia,
          mul_pow_sub_one (by lia)]
        simp [sq]
      _ = (n + n ^ 2) * 2 ^ (n - 2) := by
        rw [← add_mul, two_mul, add_add_tsub_cancel (Nat.le_pow two_pos)]
    simp_all
  · induction n, hn using Nat.le_induction
    · simp; conv => lhs; whnf
    · rename_i n hn ih; simp [Finset.Iic_eq_Icc, ← Finset.insert_Icc_add_one_left_eq_Icc (a := 0)]
      calc ∑ k ∈ Finset.Icc 1 (n + 1), k ^ 2 * (n + 1).choose k
      _ = ∑ k ∈ Finset.Icc 1 (n + 1), k ^ 2 * (n.choose (k - 1) + n.choose k) := by
        congr! 2 with k hk; simp at hk; exact Nat.choose_succ_left n k hk.left
      _ = ∑ k ∈ Finset.Icc 1 (n + 1), k ^ 2 * n.choose (k - 1) +
          ∑ k ∈ Finset.Icc 1 (n + 1), k ^ 2 * n.choose k := by simp [mul_add, Finset.sum_add_distrib]
      _ = ∑ k ≤ n, (k + 1) ^ 2 * n.choose k + ∑ k ∈ Finset.Icc 1 (n + 1), k ^ 2 * n.choose k := by
        congr 1; symm; convert Finset.sum_Ico_add _ _ _ 1 using 2; simp [add_comm]
      _ = ∑ k ≤ n, (k + 1) ^ 2 * n.choose k + ∑ k ≤ n, k ^ 2 * n.choose k := by
        simp [Finset.Iic_eq_Icc, ← Finset.insert_Icc_add_one_left_eq_Icc (a := 0),
          ← Finset.insert_Icc_right_eq_Icc_add_one, Nat.choose_eq_zero_of_lt]
      _ = 2 * ∑ k ≤ n, k ^ 2 * n.choose k + 2 * ∑ k ≤ n, k * n.choose k + ∑ k ≤ n, n.choose k := by
        simp [add_sq, add_mul, Finset.sum_add_distrib, two_mul]; ac_rfl
      _ = 2 * ((n + n ^ 2) * 2 ^ (n - 2)) + 2 * (n * 2 ^ (n - 1)) + 2 ^ n := by
        simp [ih, Zad11a, ← Nat.sum_range_choose, Nat.range_succ_eq_Iic]
      _ = (n + 1 + (n + 1) ^ 2) * 2 ^ (n - 1) := by rw [show n = n - 2 + 2 by lia]; simp; ring

theorem Zad11c (m n k : ℕ) : ∑ i ≤ k, m.choose i * n.choose (k - i) = (m + n).choose k := by
  apply and_self_iff.mp; and_intros
  · symm; calc (m + n).choose k
    _ = ((Finset.univ (α := Fin m ⊕ Fin n)).powersetCard k).card := by simp
    _ = Finset.card {s : Finset (Fin m) × Finset (Fin n) | s.1.card + s.2.card = k} := by
      apply Finset.card_equiv Finset.sumEquiv.toEquiv; intro i
      simp [i.sumEquiv_apply_fst, i.sumEquiv_apply_snd, i.card_toLeft_add_card_toRight]
    _ = ∑ i ≤ k, Finset.card {s : Finset _ × Finset _ | s.1.card = i ∧ s.2.card = k - i} := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun s => s.1.card)]
      · congr! 2; ext; grind
      · simp [Set.MapsTo]; lia
    _ = ∑ i ≤ k, Finset.card {s : Finset (Fin m) | s.card = i}
        * Finset.card {s : Finset (Fin n) | s.card = k - i} := by
      congr! with i; rw [← Finset.card_product]; congr; ext; simp
    _ = ∑ i ≤ k, m.choose i * n.choose (k - i) := by simp
  · rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.range_succ_eq_Iic]
