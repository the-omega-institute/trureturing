/- GID: D5/S3/Combinatorics/Geometry/MiuraFiberCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraFiberCore
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: All positive vectors inject into the actual two-axis residual fiber of each core. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraFiberJoint
public import D5.S3.Combinatorics.Geometry.MiuraPolynomialCoreSum
public import Mathlib.Data.Fintype.EquivFin

/-! Positive length vectors are realized by actual arrays in the existing Core fibers. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraFiberCore
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreBoundary
  MiuraCoreFrozenSlope MiuraCoreResidual MiuraCoreNormal MiuraCoreJoint
  MiuraCoreTranspose MiuraSlabIncidence MiuraFiberIndexed MiuraFiberReadback
  MiuraFiberJoint MiuraPolynomialCoreSum MiuraRunCompositions
open scoped BigOperators

private theorem inactive_run_card {m n : ℕ} (h : Cell m n → ℤ)
    (hh : IsHeight h) (hm : 0 < m) (hn : 2 ≤ n) (hno : NoAdjacentFrozen h) :
    Fintype.card {j : Fin n // ¬ activeColumn h j} = numFrozenRuns h := by
  classical
  rw [Fintype.card_subtype]
  unfold numFrozenRuns
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hj
    have hends := boundary_columns_active h hh hm hn
    have hb := inactive_internal h (by omega) hends j hj
    have hfj := inactive_imp_frozenColumn h hh j hb.1 hb.2 hm hj
    refine ⟨hj,Or.inr ⟨hb.1,?_⟩⟩
    by_contra hprev
    let k : Fin n := ⟨j.val-1,by have := j.isLt; omega⟩
    have hk := inactive_internal h (by omega) hends k hprev
    have hfk := inactive_imp_frozenColumn h hh k hk.1 hk.2 hm hprev
    exact hno ⟨k,j,by dsimp [k]; omega,hfk,hfj⟩
  · exact fun hj => hj.1

private theorem active_inactive_dimension {m n : ℕ} (h : Cell m n → ℤ) :
    numActiveColumns h + Fintype.card {j : Fin n // ¬ activeColumn h j} = n := by
  classical
  rw [Fintype.card_subtype]
  exact (Finset.card_filter_add_card_filter_not (activeColumn h) Finset.univ).trans
    (by simp)

private theorem positive_extras {m n W : ℕ} (h : Cell m n → ℤ)
    (hh : IsHeight h) (hm : 0 < m) (hn : 2 ≤ n) (hno : NoAdjacentFrozen h)
    (hW : n ≤ W) :
    ∃ e : {j : Fin n // ¬ activeColumn h j} ≃ Fin (numFrozenRuns h),
    ∀ L : PositiveLengths (W-numActiveColumns h) (numFrozenRuns h),
      ∃ w : Fin n → ℕ,
        (∀ j, 0 < w j → frozenColumn h j) ∧ n + (∑ j,w j) = W ∧
        (∀ j (hj : ¬ activeColumn h j), w j + 1 = L.val (e ⟨j,hj⟩)) := by
  classical
  let e := Fintype.equivFinOfCardEq (inactive_run_card h hh hm hn hno)
  refine ⟨e,?_⟩
  intro L
  have hR : numFrozenRuns h ≤ W-numActiveColumns h := by
    have he := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin (numFrozenRuns h) => 1)
      (g := L.val) (fun i _ => L.property.1 i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,
      L.property.2] using he
  let z := removeOnesEquiv _ _ hR L
  let w : Fin n → ℕ := fun j => if hj : activeColumn h j then 0 else z.val (e ⟨j,hj⟩)
  have hsum : (∑ j,w j) = ∑ i : {j : Fin n // ¬ activeColumn h j},z.val (e i) := by
    have hpart := Fintype.sum_subtype_add_sum_subtype (activeColumn h) w
    have hzero : (∑ i : {j : Fin n // activeColumn h j},w i.val) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp only [w,i.property,dite_true]
    rw [hzero,zero_add] at hpart
    rw [←hpart]
    apply Finset.sum_congr rfl
    intro i _
    simp only [w,i.property,dite_false]
  have hsum' : (∑ j,w j) = (W-numActiveColumns h)-numFrozenRuns h := by
    rw [hsum,e.sum_comp]
    exact z.property
  have hdim := active_inactive_dimension h
  rw [inactive_run_card h hh hm hn hno] at hdim
  refine ⟨w,?_,by omega,?_⟩
  · intro j hj
    have hja : ¬ activeColumn h j := by
      intro ha
      have : w j = 0 := by simp [w,ha]
      omega
    have hb := inactive_internal h (by omega) (boundary_columns_active h hh hm hn) j hja
    exact inactive_imp_frozenColumn h hh j hb.1 hb.2 hm hja
  · intro j hj
    simp only [w,hj,dite_false]
    change L.val (e ⟨j,hj⟩) - 1 + 1 = L.val (e ⟨j,hj⟩)
    exact Nat.sub_add_cancel (L.property.1 _)

/-- Every pair of positive length vectors of a fixed existing actual core injects
into its actual normalized residual fiber at every original large rectangle. -/
theorem core_positive_vectors_inject (a b m n : ℕ) (K : Core a b)
    (hm : 2*(a+b)-1 ≤ m) (hn : 2*(a+b)-1 ≤ n) :
    ∃ F : (PositiveLengths (m-rowOccupied K) (rowRuns K) ×
      PositiveLengths (n-colOccupied K) (colRuns K)) →
        {g : Cell m n → ℤ // Residual a b g ∧ JointReduction g K.2.2.val},
      Function.Injective F := by
  classical
  obtain ⟨hM,hN,hr,hcno,hrno,_,_⟩ := K.2.2.property
  have hMbound : K.1.val ≤ m := by have := K.1.isLt; omega
  have hNbound : K.2.1.val ≤ n := by have := K.2.1.isLt; omega
  obtain ⟨er,her⟩ := positive_extras (transposeHeight K.2.2.val)
    (transpose_isHeight hr.1.1) (by omega) hM hrno hMbound
  obtain ⟨ec,hec⟩ := positive_extras K.2.2.val hr.1.1 (by omega) hN hcno hNbound
  let V := PositiveLengths (m-rowOccupied K) (rowRuns K) ×
    PositiveLengths (n-colOccupied K) (colRuns K)
  have hex : ∀ x : V, ∃ (r : Fin K.1.val → ℕ) (c : Fin K.2.1.val → ℕ)
      (g : Cell m n → ℤ),
      (∀ i,0 < r i → frozenColumn (transposeHeight K.2.2.val) i) ∧
      (∀ j,0 < c j → frozenColumn K.2.2.val j) ∧
      K.1.val+(∑ i,r i)=m ∧ K.2.1.val+(∑ j,c j)=n ∧
      (∀ i (hi : ¬activeColumn (transposeHeight K.2.2.val) i),r i+1=x.1.val (er ⟨i,hi⟩)) ∧
      (∀ j (hj : ¬activeColumn K.2.2.val j),c j+1=x.2.val (ec ⟨j,hj⟩)) ∧
      Residual a b g ∧ JointReduction g K.2.2.val ∧ JointExtremaExpansion K.2.2.val r c g := by
    intro x
    obtain ⟨r,hrs,hrm,hrr⟩ := her x.1
    obtain ⟨c,hcs,hcn,hcc⟩ := hec x.2
    obtain ⟨g,hg,hred,he⟩ := indexed_joint_expansion a b K.2.2.val hM hN hr r c hrs hcs
    rw [hrm,hcn] at g hg hred he
    exact ⟨r,c,g,hrs,hcs,hrm,hcn,hrr,hcc,hg,hred,he⟩
  choose r c g hp using hex
  refine ⟨fun x => ⟨g x,(hp x).2.2.2.2.2.2.1,(hp x).2.2.2.2.2.2.2.1⟩,?_⟩
  intro x y hxy
  have heq : g x = g y := congrArg Subtype.val hxy
  obtain ⟨hrs,hcs,hrm,hcn,hrr,hcc,hg,hred,he⟩ := hp x
  obtain ⟨hrs',hcs',hrm',hcn',hrr',hcc',hg',hred',he'⟩ := hp y
  have huw := indexed_joint_weights_unique K.2.2.val hr.1.1 hM hN hrno hcno
    (r x) (r y) (c x) (c y) hrs hrs' hcs hcs' (g x)
    hrm.symm hrm'.symm hcn.symm hcn'.symm he (heq.symm ▸ he')
  apply Prod.ext <;> apply Subtype.ext
  · funext i
    obtain ⟨j,hj⟩ := er.surjective i
    have ha := hrr j.val j.property
    have hb := hrr' j.val j.property
    rw [hj] at ha hb
    rw [huw.1] at ha
    omega
  · funext i
    obtain ⟨j,hj⟩ := ec.surjective i
    have ha := hcc j.val j.property
    have hb := hcc' j.val j.property
    rw [hj] at ha hb
    rw [huw.2] at ha
    omega

end D5.S3.Combinatorics.Geometry.MiuraFiberCore
