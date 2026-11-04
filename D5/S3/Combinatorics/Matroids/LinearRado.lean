/- GID: D5/S3/Combinatorics/Matroids/LinearRado
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/LinearRado
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dimension Hall inequalities yield spanning representatives. -/

/- admission_basis: escape-witness (linear_rado_finset)
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22087
   Module escape_witness: linear_rado_finset
   Direct frozen dependencies: none.
   familySum_map: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: linear_rado_finset.
   quotient_sum_finrank: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: linear_rado_finset.
   glue: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: linear_rado_finset.
   linear_rado_finset: proof_shape: content; escape_witness: linear_rado_finset;
     Direct frozen dependencies: none.
     consumers: linear_rado.
   linear_rado: proof_shape: content; escape_witness: linear_rado;
     Direct frozen dependencies: none.
     consumers: spanning_representatives.
   iSup_prod_top: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: spanning_representatives.
   spanning_representatives: proof_shape: content; escape_witness: spanning_representatives;
     Direct frozen dependencies: none.
     consumers: generic_minor_nonzero.
   exists_nonsingular_rows: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: generic_minor_nonzero, independent_support_matching.
   independent_support_matching: proof_shape: bind-only; escape_witness: none;
     Direct frozen dependencies: none.
     consumers: partial_of_imageRank.
-/

import Mathlib.LinearAlgebra.Matrix.Rank

namespace D5.S3.Combinatorics.Matroids.LinearRado

open Module Submodule
section
universe u v w
variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {ι : Type w}

omit [FiniteDimensional F V] in
private lemma familySum_map {W : Type*} [AddCommGroup W] [Module F W]
    (E : ι → Submodule F V) (s : Finset ι) (f : V →ₗ[F] W) :
    (s.sup (fun i => (E i).map f)) = ((s.sup E)).map f := by
  simp only [Finset.sup_eq_iSup, Submodule.map_iSup]

private lemma quotient_sum_finrank (H S : Submodule F V) :
    finrank F (S.map H.mkQ) + finrank F H = finrank F (S ⊔ H : Submodule F V) := by
  have h := (H.mkQ.domRestrict (S ⊔ H)).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, Submodule.map_sup, H.mkQ_map_self, sup_bot_eq,
    LinearMap.ker_domRestrict, H.ker_mkQ] at h
  rw [← (Submodule.comapSubtypeEquivOfLe (show H ≤ S ⊔ H from le_sup_right)).finrank_eq]
  exact h

omit [FiniteDimensional F V] in
private lemma glue {s t : Finset ι} [DecidableEq ι] (hts : t ⊆ s)
    (E : ι → Submodule F V) (H : Submodule F V)
    (a : t → H) (ha : ∀ i : t, (a i : V) ∈ E i.1) (hai : LinearIndependent F a)
    (b : ↥(s \ t) → V) (hb : ∀ i : ↥(s \ t), b i ∈ E i.1)
    (hbi : LinearIndependent F (H.mkQ ∘ b)) :
    ∃ e : s → V, (∀ i : s, e i ∈ E i.1) ∧ LinearIndependent F e := by
  let equiv : ↥t ⊕ ↥(s \ t) ≃ ↥s :=
    (Equiv.sumCongr (Equiv.refl _) (Set.equivOfEq (Finset.coe_sdiff s t))).trans
      (Equiv.Set.sumDiffSubset (show (t : Set ι) ⊆ (s : Set ι) from hts))
  let e := Sum.elim (fun i => (a i : V)) b
  refine ⟨e ∘ equiv.symm, ?_, ?_⟩
  · intro i
    obtain ⟨i, rfl⟩ := equiv.surjective i
    cases i with
    | inl i =>
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      exact ha i
    | inr i =>
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      exact hb i
  · exact (hai.sumElim_of_quotient b hbi).comp equiv.symm equiv.symm.injective

end


open Module Submodule
section
universe u v w
variable {F : Type u} [Field F] {ι : Type w} [DecidableEq ι]

/-- Linear Rado, for a finite set of indices, by quotient induction. -/
private theorem linear_rado_finset {V : Type v} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : Finset ι) (E : ι → Submodule F V)
    (hall : ∀ J : Finset ι, J ⊆ s → J.card ≤ finrank F ↥(J.sup E)) :
    ∃ e : s → V, (∀ i : s, e i ∈ E i.1) ∧ LinearIndependent F e := by
  classical
  induction s using Finset.strongInduction generalizing V with
  | H s ih =>
    by_cases hs : s = ∅
    · subst s
      refine ⟨fun i => False.elim (Finset.notMem_empty i.1 i.2), ?_, ?_⟩
      · intro i
        exact False.elim (Finset.notMem_empty i.1 i.2)
      · exact linearIndependent_empty_type
    by_cases htight : ∃ t : Finset ι, t ⊂ s ∧ t.Nonempty ∧
        finrank F ↥(t.sup E) = t.card
    · obtain ⟨t, hts, htne, htdim⟩ := htight
      obtain ⟨a, ha, hai⟩ := ih t hts E (fun J hJ => hall J (hJ.trans hts.subset))
      let H := (t.sup E)
      let aH : t → H := fun i => ⟨a i,
        (show E i.1 ≤ (t.sup E) from
          Finset.le_sup (f := E) i.2) (ha i)⟩
      have haHi : LinearIndependent F aH := by
        exact LinearIndependent.of_comp H.subtype hai
      have hrem : s \ t ⊂ s := Finset.sdiff_ssubset (hts.subset) htne
      have hquot : ∀ J : Finset ι, J ⊆ s \ t →
          J.card ≤ finrank F ↥(J.sup (fun i => (E i).map H.mkQ)) := by
        intro J hJ
        have hd : Disjoint t J := by
          exact Finset.disjoint_left.mpr fun i hit hiJ =>
            (Finset.mem_sdiff.mp (hJ hiJ)).2 hit
        have hbound := hall (t ∪ J) (Finset.union_subset hts.subset (hJ.trans Finset.sdiff_subset))
        rw [Finset.card_union_of_disjoint hd, Finset.sup_union] at hbound
        have hdim := quotient_sum_finrank H ((J.sup E))
        rw [← familySum_map] at hdim
        change finrank F ↥(J.sup (fun i => (E i).map H.mkQ)) +
          finrank F ↥(t.sup E) = finrank F ((J.sup E) ⊔ (t.sup E) : Submodule F V) at hdim
        rw [sup_comm] at hdim
        omega
      obtain ⟨q, hq, hqi⟩ := ih (s \ t) hrem (fun i => (E i).map H.mkQ) hquot
      have hlift : ∀ i : (s \ t : Finset ι), ∃ v ∈ E i.1, H.mkQ v = q i := by
        intro i
        exact hq i
      choose b hb hbeq using hlift
      have hbi : LinearIndependent F (H.mkQ ∘ b) := by
        simpa only [Function.comp_def, hbeq] using hqi
      exact glue hts.subset E H aH ha haHi b hb hbi
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have hidim := hall {i} (Finset.singleton_subset_iff.mpr hi)
      have hsingle : ({i} : Finset ι).sup E = E i := Finset.sup_singleton
      have hidim' : 0 < finrank F (E i) := by
        rw [Finset.card_singleton, hsingle] at hidim
        omega
      have hEi : E i ≠ ⊥ := Submodule.one_le_finrank_iff.mp hidim'
      obtain ⟨v, hv, hv0⟩ := (E i).ne_bot_iff.mp hEi
      let H : Submodule F V := Submodule.span F {v}
      have hHdim : finrank F H = 1 := finrank_span_singleton hv0
      have hrem : s \ {i} ⊂ s :=
        Finset.sdiff_ssubset (Finset.singleton_subset_iff.mpr hi) (Finset.singleton_nonempty i)
      have hquot : ∀ J : Finset ι, J ⊆ s \ {i} →
          J.card ≤ finrank F ↥(J.sup (fun i => (E i).map H.mkQ)) := by
        intro J hJ
        by_cases hJne : J.Nonempty
        · have hJs : J ⊂ s := lt_of_le_of_lt hJ hrem
          have hbound := hall J hJs.subset
          have hnot : finrank F ↥(J.sup E) ≠ J.card := by
            intro he
            exact htight ⟨J, hJs, hJne, he⟩
          have hle := Submodule.finrank_mono (show (J.sup E) ≤ (J.sup E) ⊔ H from le_sup_left)
          have hdim := quotient_sum_finrank H ((J.sup E))
          rw [← familySum_map, hHdim] at hdim
          omega
        · simp only [Finset.not_nonempty_iff_eq_empty] at hJne
          simp [hJne]
      obtain ⟨q, hq, hqi⟩ := ih (s \ {i}) hrem (fun i => (E i).map H.mkQ) hquot
      have hlift : ∀ j : (s \ {i} : Finset ι), ∃ v ∈ E j.1, H.mkQ v = q j := by
        intro j
        exact hq j
      choose b hb hbeq using hlift
      have hbi : LinearIndependent F (H.mkQ ∘ b) := by
        simpa only [Function.comp_def, hbeq] using hqi
      let a : ({i} : Finset ι) → H := fun _ => ⟨v, Submodule.subset_span (by simp)⟩
      have ha : ∀ j : ({i} : Finset ι), (a j : V) ∈ E j.1 := by
        intro j
        have hj : j.1 = i := Finset.mem_singleton.mp j.2
        simpa [a, hj] using hv
      have hai : LinearIndependent F a := by
        apply (linearIndependent_subsingleton_index_iff a).mpr
        intro j hj
        exact hv0 (congrArg (fun x : H => (x : V)) hj)
      exact glue (Finset.singleton_subset_iff.mpr hi) E H a ha hai b hb hbi

/-- The finite-family form used by the annihilator construction. -/
private theorem linear_rado {V : Type v} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {n : ℕ} (E : Fin n → Submodule F V)
    (hall : ∀ J : Finset (Fin n), J.card ≤
      finrank F (↥(⨆ i : {i : Fin n // i ∈ J}, E i.1))) :
    ∃ e : Fin n → V, (∀ i, e i ∈ E i) ∧ LinearIndependent F e := by
  classical
  obtain ⟨e, he, hei⟩ := linear_rado_finset Finset.univ E (fun J _ => by
    have hsum : (J.sup E) = ⨆ i : {i : Fin n // i ∈ J}, E i.1 := by
      exact (Finset.sup_eq_iSup J E).trans (iSup_subtype (p := fun i => i ∈ J) (f := fun i => E i.1)).symm
    rw [hsum]
    exact hall J)
  let f : Fin n → (Finset.univ : Finset (Fin n)) := fun i => ⟨i, Finset.mem_univ i⟩
  refine ⟨e ∘ f, fun i => he (f i), hei.comp f ?_⟩
  intro i j hij
  exact congrArg Subtype.val hij

end


open Module Submodule
section
universe u v w z

private lemma iSup_prod_top {F : Type u} [Field F] {W : Type v} {A : Type w}
    [AddCommGroup W] [Module F W] [AddCommGroup A] [Module F A]
    {ι : Type z} [Nonempty ι] (L : ι → Submodule F W) :
    (⨆ i, (L i).prod (⊤ : Submodule F A)) = (⨆ i, L i).prod (⊤ : Submodule F A) := by
  apply le_antisymm
  · exact iSup_le fun i => Submodule.prod_mono (le_iSup L i) le_rfl
  · intro x hx
    have hleft : (⨆ i, L i).map (LinearMap.inl F W A) ≤
        ⨆ i, (L i).prod (⊤ : Submodule F A) := by
      rw [Submodule.map_iSup]
      apply iSup_le
      intro i
      rintro y ⟨w, hw, rfl⟩
      exact (le_iSup (fun i => (L i).prod (⊤ : Submodule F A)) i) ⟨hw, trivial⟩
    have h1 : (x.1, 0) ∈ ⨆ i, (L i).prod (⊤ : Submodule F A) :=
      hleft (Submodule.mem_map.mpr ⟨x.1, hx.1, rfl⟩)
    have h2 : (0, x.2) ∈ ⨆ i, (L i).prod (⊤ : Submodule F A) :=
      (le_iSup (fun i => (L i).prod (⊤ : Submodule F A)) (Classical.arbitrary ι))
        ⟨(L _).zero_mem, trivial⟩
    simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using
      (⨆ i, (L i).prod (⊤ : Submodule F A)).add_mem h1 h2

/-- Deficit Hall inequalities produce one representative per subspace spanning the ambient space. -/
theorem spanning_representatives {F : Type u} [Field F] {W : Type v}
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] {k : ℕ}
    (L : Fin k → Submodule F W) (ht : finrank F W ≤ k)
    (hall : ∀ J : Finset (Fin k), finrank F W + J.card ≤ k +
      finrank F (↥(⨆ i : {i : Fin k // i ∈ J}, L i.1))) :
    ∃ l : Fin k → W, (∀ i, l i ∈ L i) ∧ Submodule.span F (Set.range l) = ⊤ := by
  classical
  let A := Fin (k - finrank F W) → F
  let E : Fin k → Submodule F (W × A) := fun i => (L i).prod ⊤
  have hA : finrank F A = k - finrank F W := Module.finrank_fin_fun F
  have hE : ∀ J : Finset (Fin k), J.card ≤ finrank F (↥(⨆ i : {i : Fin k // i ∈ J}, E i.1)) := by
    intro J
    by_cases hJ : J.Nonempty
    · haveI : Nonempty J := hJ.coe_sort
      have hsum : (⨆ i : {i : Fin k // i ∈ J}, E i.1) =
          (⨆ i : {i : Fin k // i ∈ J}, L i.1).prod (⊤ : Submodule F A) := iSup_prod_top _
      rw [hsum, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod,
        finrank_top, hA]
      have hbound := hall J
      omega
    · have hzero : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      rw [hzero, Finset.card_empty]
      exact Nat.zero_le _
  obtain ⟨e, he, hei⟩ := linear_rado E hE
  have hdim : Fintype.card (Fin k) = finrank F (W × A) := by
    rw [Fintype.card_fin, Module.finrank_prod, hA]
    omega
  have hspan := hei.span_eq_top_of_card_eq_finrank' hdim
  let l := fun i => (e i).1
  refine ⟨l, fun i => (he i).1, ?_⟩
  have hmap := congrArg (Submodule.map (LinearMap.fst F W A)) hspan
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top] at hmap
  rw [LinearMap.range_eq_top.mpr (show Function.Surjective (LinearMap.fst F W A) from fun w => ⟨(w, 0), rfl⟩)] at hmap
  exact hmap

end


open Module Submodule
section

/-- A spanning finite family of rows contains a nonsingular maximal square minor. -/
theorem exists_nonsingular_rows {F : Type*} [Field F] {k t : ℕ}
    (M : Matrix (Fin k) (Fin t) F)
    (hM : Submodule.span F (Set.range M.row) = ⊤) :
    ∃ f : Fin t → Fin k, Function.Injective f ∧ (M.submatrix f id).det ≠ 0 := by
  classical
  obtain ⟨κ, a, hai, hspan, hLI⟩ := exists_linearIndependent' F M.row
  haveI : Finite κ := hLI.finite
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = t := by
    have hdim := finrank_span_eq_card hLI
    rw [hspan, hM, finrank_top, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at hdim
    exact hdim.symm
  let e : Fin t ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let f : Fin t → Fin k := a ∘ e
  have hfi : Function.Injective f := hai.comp e.injective
  have hA : LinearIndependent F (M.submatrix f id).row := hLI.comp e e.injective
  have hunit : IsUnit (M.submatrix f id) := Matrix.linearIndependent_row_iff_isUnit.mp hA
  exact ⟨f, hfi, ((M.submatrix f id).isUnit_iff_isUnit_det.mp hunit).ne_zero⟩

end


section
open Module Submodule

theorem independent_support_matching {K : Type*} [Field K]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → (κ → K))
    (hv : LinearIndependent K v) :
    ∃ f : ι → κ, Function.Injective f ∧ ∀ i, v i (f i) ≠ 0 := by
  classical
  let ei := Fintype.equivFin ι
  let ek := Fintype.equivFin κ
  let M : Matrix (Fin (Fintype.card κ)) (Fin (Fintype.card ι)) K :=
    fun i j => v (ei.symm j) (ek.symm i)
  have hcols : LinearIndependent K M.col := by
    exact ((hv.comp ei.symm ei.symm.injective).map'
      (LinearEquiv.funCongrLeft K K ek.symm).toLinearMap
      (LinearEquiv.ker _))
  have hrank : M.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hcols, Fintype.card_fin]
  have hrows : span K (Set.range M.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_pi, Fintype.card_fin]
  obtain ⟨f, hf, hdet⟩ := exists_nonsingular_rows M hrows
  rw [Matrix.det_apply'] at hdet
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hp : ∏ i, (M.submatrix f id) (σ i) i ≠ 0 := (mul_ne_zero_iff.mp hσ).2
  have hn (i : Fin (Fintype.card ι)) : M (f (σ i)) i ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ _)
  refine ⟨fun i => ek.symm (f (σ (ei i))), ek.symm.injective.comp (hf.comp (σ.injective.comp ei.injective)), ?_⟩
  intro i
  simpa [M] using hn (ei i)

end

end D5.S3.Combinatorics.Matroids.LinearRado
