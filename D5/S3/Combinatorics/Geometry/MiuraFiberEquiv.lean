/- GID: D5/S3/Combinatorics/Geometry/MiuraFiberEquiv
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraFiberEquiv
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive run vectors are equivalent to the entire existing actual fixed-core fiber. -/
module
public import D5.S3.Combinatorics.Geometry.MiuraFiberInverseExpansion
import all D5.S3.Combinatorics.Geometry.MiuraFiberCore
import all D5.S3.Combinatorics.Geometry.MiuraFiberJoint

/-! Exact geometric readback and realization on the same individual height functions. -/
@[expose] public section
namespace D5.S3.Combinatorics.Geometry.MiuraFiberEquiv
open MiuraHeightEnvelope MiuraResidualCount MiuraCoreColumns MiuraCoreContract
  MiuraCoreCellExpand MiuraCoreExtremum MiuraCoreResidual MiuraCoreNormal MiuraCoreJoint
  MiuraCoreTranspose MiuraSlabIncidence MiuraFiberIndexed MiuraFiberReadback
  MiuraFiberJoint MiuraPolynomialCoreSum MiuraRunCompositions MiuraCoreRestore
  MiuraCanonicalJoint MiuraCanonicalColumns MiuraCoreFrozenSlope MiuraFiberInverse
  MiuraCoreBoundary MiuraFiberInverseExpansion MiuraFiberCore
open private positive_extras inactive_run_card active_inactive_dimension joint_sides
  from D5.S3.Combinatorics.Geometry.MiuraFiberCore
open private joint_active_images from D5.S3.Combinatorics.Geometry.MiuraFiberJoint
open scoped BigOperators

private theorem supported_zero {m n : ℕ} (h : Cell m n → ℤ) (w : Fin n → ℕ)
    (hw : ∀ j, 0 < w j → frozenColumn h j) (j : Fin n) (hj : activeColumn h j) : w j = 0 := by
  by_contra he
  exact frozenColumn_not_active h j (hw j (Nat.pos_of_ne_zero he)) hj

private theorem weights_lengths {m n W : ℕ} (h : Cell m n → ℤ)
    (hh : IsHeight h) (hm : 0 < m) (hn : 2 ≤ n) (hno : NoAdjacentFrozen h)
    (e : {j : Fin n // ¬ activeColumn h j} ≃ Fin (numFrozenRuns h))
    (w : Fin n → ℕ) (hw : ∀ j, 0 < w j → frozenColumn h j)
    (hdim : W = n + ∑ j, w j) :
    ∃ L : PositiveLengths (W - numActiveColumns h) (numFrozenRuns h),
      ∀ j (hj : ¬ activeColumn h j), w j + 1 = L.val (e ⟨j, hj⟩) := by
  classical
  let L : Fin (numFrozenRuns h) → ℕ := fun i => w (e.symm i).val + 1
  have hsum : (∑ j, w j) = ∑ i : {j : Fin n // ¬ activeColumn h j}, w i.val := by
    have H := Fintype.sum_subtype_add_sum_subtype (activeColumn h) w
    have hz : (∑ i : {j : Fin n // activeColumn h j}, w i.val) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact supported_zero h w hw i.val i.property
    rw [hz, zero_add] at H
    exact H.symm
  have hdim' := active_inactive_dimension h
  rw [inactive_run_card h hh hm hn hno] at hdim'
  have hLsum : (∑ i, L i) = W - numActiveColumns h := by
    have H : (∑ i : Fin (numFrozenRuns h), w (e.symm i).val) = ∑ j, w j := by
      rw [hsum]
      exact e.symm.sum_comp (fun i => w i.val)
    simp only [L, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one, H]
    omega
  refine ⟨⟨L, ⟨by intro i; dsimp [L]; omega, hLsum⟩⟩, ?_⟩
  intro j hj
  simp only [L, e.symm_apply_apply]

/-- The inverse reads every run length from the actual occupied positions. Its forward
map realizes those lengths and recovers every original height value. -/
theorem core_positive_vectors_equiv (a b m n : ℕ) (K : Core a b)
    (hm : 2*(a + b)-1 ≤ m) (hn : 2*(a + b)-1 ≤ n) :
    Nonempty ((PositiveLengths (m - rowOccupied K) (rowRuns K) ×
      PositiveLengths (n - colOccupied K) (colRuns K)) ≃
        {g : Cell m n → ℤ // Residual a b g ∧ JointReduction g K.2.2.val ∧
          ∀ sd, AllOnSide (fun v : Cell m n => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
            (minima g) (m : ℤ) (n : ℤ) sd ↔
          AllOnSide (fun v : Cell K.1.val K.2.1.val => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
            (minima K.2.2.val) (K.1.val : ℤ) (K.2.1.val : ℤ) sd}) := by
  classical
  obtain ⟨hM, hN, hr, hcno, hrno, _, _⟩ := K.2.2.property
  have hMbound : K.1.val ≤ m := by have := K.1.isLt; omega
  have hNbound : K.2.1.val ≤ n := by have := K.2.1.isLt; omega
  obtain ⟨er, her⟩ := positive_extras (transposeHeight K.2.2.val)
    (transpose_isHeight hr.1.1) (by omega) hM hrno hMbound
  obtain ⟨ec, hec⟩ := positive_extras K.2.2.val hr.1.1 (by omega) hN hcno hNbound
  let V := PositiveLengths (m - rowOccupied K) (rowRuns K) ×
    PositiveLengths (n - colOccupied K) (colRuns K)
  let F := {g : Cell m n → ℤ // Residual a b g ∧ JointReduction g K.2.2.val ∧
    ∀ sd, AllOnSide (fun v : Cell m n => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
      (minima g) (m : ℤ) (n : ℤ) sd ↔
    AllOnSide (fun v : Cell K.1.val K.2.1.val => ((v.1.val : ℤ) + 1, (v.2.val : ℤ) + 1))
      (minima K.2.2.val) (K.1.val : ℤ) (K.2.1.val : ℤ) sd}
  have read : ∀ g : F, ∃ (r : Fin K.1.val → ℕ) (c : Fin K.2.1.val → ℕ),
      (∀ i, 0 < r i → frozenColumn (transposeHeight K.2.2.val) i) ∧
      (∀ j, 0 < c j → frozenColumn K.2.2.val j) ∧
      m = K.1.val + ∑ i, r i ∧ n = K.2.1.val + ∑ j, c j ∧
      (∀ k, activeColumn g.val k ↔ ∃ j, activeColumn K.2.2.val j ∧ k.val = columnPosition c j) ∧
      (∀ k, activeColumn (transposeHeight g.val) k ↔
        ∃ i, activeColumn (transposeHeight K.2.2.val) i ∧ k.val = columnPosition r i) := by
    intro g
    exact reduction_indexed_active a b g.val K.2.2.val g.property.2.1
      (by omega) (by omega) g.property.1 hM hN hr.1.1
  choose r c hp using read
  have lr : ∀ g : F, ∃ L : PositiveLengths (m - rowOccupied K) (rowRuns K),
      ∀ i (hi : ¬ activeColumn (transposeHeight K.2.2.val) i), r g i + 1 = L.val (er ⟨i, hi⟩) := by
    intro g
    exact weights_lengths (transposeHeight K.2.2.val) (transpose_isHeight hr.1.1)
      (by omega) hM hrno er (r g) (hp g).1 (hp g).2.2.1
  have lc : ∀ g : F, ∃ L : PositiveLengths (n - colOccupied K) (colRuns K),
      ∀ j (hj : ¬ activeColumn K.2.2.val j), c g j + 1 = L.val (ec ⟨j, hj⟩) := by
    intro g
    exact weights_lengths K.2.2.val hr.1.1 (by omega) hN hcno ec (c g)
      (hp g).2.1 (hp g).2.2.2.1
  choose Lr hLr using lr
  choose Lc hLc using lc
  let G : F → V := fun g => (Lr g, Lc g)
  have hinj : Function.Injective G := by
    intro g f he
    have heR : r g = r f := by
      funext i
      by_cases hi : activeColumn (transposeHeight K.2.2.val) i
      · rw [supported_zero _ (r g) (hp g).1 i hi, supported_zero _ (r f) (hp f).1 i hi]
      · have H := congrArg (fun x : V => x.1.val (er ⟨i, hi⟩)) he
        have Hg := hLr g i hi
        have Hf := hLr f i hi
        change (Lr g).val _ = (Lr f).val _ at H
        omega
    have heC : c g = c f := by
      funext j
      by_cases hj : activeColumn K.2.2.val j
      · rw [supported_zero _ (c g) (hp g).2.1 j hj, supported_zero _ (c f) (hp f).2.1 j hj]
      · have H := congrArg (fun x : V => x.2.val (ec ⟨j, hj⟩)) he
        have Hg := hLc g j hj
        have Hf := hLc f j hj
        change (Lc g).val _ = (Lc f).val _ at H
        omega
    apply Subtype.ext
    apply same_core_same_active_equal a b g.val f.val (by omega) (by omega)
      g.property.1 f.property.1 K.2.2.val hcno hrno g.property.2.1 f.property.2.1
    · intro j
      exact ((hp g).2.2.2.2.1 j).trans (by rw [heC]; exact ((hp f).2.2.2.2.1 j).symm)
    · intro i
      exact ((hp g).2.2.2.2.2 i).trans (by rw [heR]; exact ((hp f).2.2.2.2.2 i).symm)
  have hsurj : Function.Surjective G := by
    intro x
    obtain ⟨r', hrs, hrm, hrr⟩ := her x.1
    obtain ⟨c', hcs, hcn, hcc⟩ := hec x.2
    have H := indexed_joint_expansion a b K.2.2.val hM hN hr r' c' hrs hcs
    rw [hrm, hcn] at H
    obtain ⟨g, hg, hred, he⟩ := H
    let z : F := ⟨g, hg, hred, joint_sides hred hg.1.1⟩
    have hactive := joint_active_images K.2.2.val r' c' g hrm.symm hcn.symm he
    have hwr : r z = r' := indexed_column_weights_unique (transposeHeight K.2.2.val)
      (transpose_isHeight hr.1.1) (by omega) hM hrno (r z) r' (hp z).1 hrs
      (transposeHeight g) (hp z).2.2.1 hrm.symm (hp z).2.2.2.2.2 hactive.2
    have hwc : c z = c' := indexed_column_weights_unique K.2.2.val hr.1.1
      (by omega) hN hcno (c z) c' (hp z).2.1 hcs g
      (hp z).2.2.2.1 hcn.symm (hp z).2.2.2.2.1 hactive.1
    refine ⟨z, Prod.ext ?_ ?_⟩ <;> apply Subtype.ext <;> funext i
    · obtain ⟨j, hj⟩ := er.surjective i
      have H1 := hLr z j.val j.property
      have H2 := hrr j.val j.property
      rw [hj, hwr] at H1
      rw [hj] at H2
      exact H1.symm.trans H2
    · obtain ⟨j, hj⟩ := ec.surjective i
      have H1 := hLc z j.val j.property
      have H2 := hcc j.val j.property
      rw [hj, hwc] at H1
      rw [hj] at H2
      exact H1.symm.trans H2
  exact ⟨(Equiv.ofBijective G ⟨hinj, hsurj⟩).symm⟩

end D5.S3.Combinatorics.Geometry.MiuraFiberEquiv
