/- GID: D5/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood
   generality: S
   mirror-B: D5/B/S3/HardCoreHolomorphic/AdaptiveComplexNeighborhood
   mirror-E: none(waiver:actual-finite-type-holomorphic-neighborhood)
   anchors: []
   digest: The actual 881 grid types admit a common explicit activity tube and invariant complex messages. -/

import D5.S3.HardCoreHolomorphic.InvariantTube
import D5.S3.StatisticalMechanics.HardCore.AdaptiveAffineMessages

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable section
namespace D5.S3.HardCoreHolomorphic.AdaptiveComplexNeighborhood
open scoped BigOperators
open D5.S3.HardCoreHolomorphic.AffineChart
open D5.S3.HardCoreHolomorphic.TypedJacobian
open D5.S3.HardCoreHolomorphic.TubeEstimates
open D5.S3.HardCoreHolomorphic.RowTubeBounds
open D5.S3.HardCoreHolomorphic.InvariantTube
open D5.S3.StatisticalMechanics.HardCore.AdaptiveAffineMessageData
open D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates
open D5.S3.StatisticalMechanics.HardCore.AdaptiveAffineMessages

private def aa (i : Fin 881) : ℝ := (affineCoefficients i).1
private def bb (i : Fin 881) : ℝ := (affineCoefficients i).2

-- Split the finite quantifier before deciding: each leaf is checked by the kernel
-- in its own auxiliary theorem, without elaborating 881 simultaneous goals.
local syntax "decide_each" num : tactic
local macro_rules
  | `(tactic| decide_each $n:num) => do
    let k := n.getNat
    if k ≤ 1 then `(tactic| decide +kernel)
    else
      let a := Lean.Syntax.mkNumLit (toString (k / 2))
      let b := Lean.Syntax.mkNumLit (toString (k - k / 2))
      `(tactic| exact (Fin.forall_fin_add (m := $a:num) (n := $b:num) _).mpr
          ⟨by decide_each $a, by decide_each $b⟩)

private theorem coefficient_upper : ∀ j : Fin 881, (affineCoefficients j).2 ≤ (3:ℚ) := by
  decide_each 881

/-- The analytic estimate uses this additional exact bound on the same payload.
The lower bound and slope sign are reused from the existing full-box certificate. -/
theorem actual_coefficient_bounds (i : Fin 881) : CoeffBound (aa i) (bb i) := by
  have hb := coefficient_upper
  have h := affine_message_certificate i
  have ha : (0:ℝ) ≤ aa i := by
    dsimp [aa]
    exact_mod_cast h.1
  have hc : (10577/1000000:ℝ) ≤ bb i-aa i := by
    have hR := (Rat.cast_le (K := ℝ)).mpr h.2.1
    simpa only [aa, bb, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat] using hR
  have hb' : bb i ≤ (3:ℝ) := by
    dsimp [bb]
    exact_mod_cast hb i
  exact ⟨ha,by linarith,hb'⟩

/-- A subset of actual geometric children. The root is separately treated. -/
def Pruning (i : Fin 881) (s : Finset (Fin 3)) : Prop :=
  ∀ d ∈ s, ∃ j, radiusFourStep i (radiusFourChoice i) d = some j

/-- Total accessor, used only on genuine children by Pruning. -/
def childType (i : Fin 881) (d : Fin 3) : Fin 881 :=
  (radiusFourStep i (radiusFourChoice i) d).getD 0

/-- Explicit open tube around each actual type's compact real chart image. -/
def Omega (i : Fin 881) : Set ℂ :=
  {m | ∃ x : ℝ, x ∈ Set.Icc (20/71) 1 ∧ ‖m-center (aa i) (bb i) x‖ < delta}

/-- One open activity neighborhood, independent of graph size and recursion depth. -/
def ActivityTube : Set ℂ :=
  {z | ∃ lam : ℝ, lam ∈ Set.Icc 0 (51/20) ∧ ‖z-(lam:ℂ)‖ < epsilon}

/-- The actual transformed map for the supplied geometric parent and child subset. -/
def adaptiveMap (i : Fin 881) (s : Finset (Fin 3)) (z : ℂ) (m : Fin 3 → ℂ) : ℂ :=
  rowMap s (aa i) (bb i) (fun d => aa (childType i d)) (fun d => bb (childType i d)) z m

private theorem tube_open {α : Type*} (S : Set α) (c : α → ℂ) (e : ℝ) :
    IsOpen {z | ∃ x ∈ S, ‖z-c x‖ < e} := by
  have h : {z | ∃ x ∈ S, ‖z-c x‖ < e} = ⋃ x ∈ S, Metric.ball (c x) e := by
    ext z; simp [Metric.mem_ball,dist_eq_norm]
  rw [h]
  exact isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => Metric.isOpen_ball))

/-- The constructed message and activity domains really are open. -/
theorem neighborhoods_open : (∀ i, IsOpen (Omega i)) ∧ IsOpen ActivityTube := by
  exact ⟨fun i => tube_open (Set.Icc (20/71:ℝ) 1) (center (aa i) (bb i)) delta,
    tube_open (Set.Icc (0:ℝ) (51/20)) (fun x:ℝ => (x:ℂ)) epsilon⟩

private theorem real_row (i : Fin 881) (s : Finset (Fin 3)) (hs : Pruning i s)
    (r : Fin 3 → ℝ) (hr : ∀ d ∈ s, 20/71 ≤ r d ∧ r d ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 51/20) :
    (∑ d ∈ s, ‖((-(lam*(∏ k ∈ s, r k)*
      (bb (childType i d)-aa (childType i d)*r d)) /
      (bb i-aa i+bb i*lam*(∏ k ∈ s, r k)):ℝ):ℂ)‖) ≤ 999/1000 := by
  let x : Fin 3 → ℝ := fun d => if d ∈ s then r d else 1
  have hx (d) : (20/71:ℝ) ≤ x d ∧ x d ≤ 1 := by
    by_cases hd : d ∈ s
    · simpa [x,hd] using hr d hd
    · norm_num [x,hd]
  have he (d) (hd : d ∈ s) : childMessage i d (r d) =
      bb (childType i d)-aa (childType i d)*r d := by
    obtain ⟨j,hj⟩ := hs d hd
    simp [childMessage,childCoefficients,childType,hj,aa,bb]
  have hp : (∏ d, x d) = ∏ d ∈ s, r d := by simp [x]
  have hxmask : (fun d => if d ∈ s then x d else 1) = x := by
    funext d
    by_cases hd : d ∈ s <;> simp [x, hd]
  have hrow := affine_pruned_row_contraction i s lam hlam x hx
  dsimp only at hrow
  rw [hxmask] at hrow
  have hsum : (∑ d ∈ s, childMessage i d (x d)) =
      ∑ d ∈ s, (bb (childType i d)-aa (childType i d)*r d) := by
    apply Finset.sum_congr rfl
    intro d hd; simpa [x,hd] using he d hd
  rw [hsum] at hrow
  let P : ℝ := ∏ d ∈ s, r d
  have hP : 0 ≤ P := Finset.prod_nonneg (fun d hd => by linarith [(hr d hd).1])
  have hb : 0 < bb i := by
    have hc := actual_coefficient_bounds i; dsimp [CoeffBound] at hc; linarith
  have hH : 0 < bb i-aa i+bb i*lam*P := by
    have hc := (actual_coefficient_bounds i).2.1
    nlinarith [mul_nonneg (mul_nonneg hb.le hlam.1) hP]
  have hD : 1+lam*P ≠ 0 := ne_of_gt (by nlinarith [mul_nonneg hlam.1 hP])
  have hnon (d) (hd : d ∈ s) : 0 ≤ bb (childType i d)-aa (childType i d)*r d := by
    have c := actual_coefficient_bounds (childType i d)
    nlinarith [mul_le_mul_of_nonneg_left (hr d hd).2 c.1, c.2.1]
  have heq : (∑ d ∈ s, ‖((-(lam*P*(bb (childType i d)-aa (childType i d)*r d)) /
      (bb i-aa i+bb i*lam*P):ℝ):ℂ)‖) =
      (1-vacancy lam x)*(∑ d ∈ s, (bb (childType i d)-aa (childType i d)*r d)) /
        affineMessage i (vacancy lam x) := by
    calc
      _ = ∑ d ∈ s, (lam*P*(bb (childType i d)-aa (childType i d)*r d)) /
          (bb i-aa i+bb i*lam*P) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hn := mul_nonneg (mul_nonneg hlam.1 hP) (hnon d hd)
        simp only [Complex.norm_real,Real.norm_eq_abs,neg_div,
          abs_neg,abs_of_nonneg (div_nonneg hn hH.le)]
      _ = _ := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
        dsimp only [affineMessage, vacancy]
        rw [hp]
        change lam*P*(∑ d ∈ s, (bb (childType i d)-aa (childType i d)*r d)) /
            (bb i-aa i+bb i*lam*P) =
          (1-1/(1+lam*P))*(∑ d ∈ s, (bb (childType i d)-aa (childType i d)*r d)) /
            (bb i-aa i*(1/(1+lam*P)))
        field_simp (disch := first | assumption | (convert ne_of_gt hH using 1; ring1))
        ring
  rw [heq]
  exact hrow.le

/-- Every actual type and every allowed pruning has the same invariant complex
neighborhood. Its widths are explicit: delta=10^-20, epsilon=10^-30.
No existence, Lipschitz, holomorphy or complex-invariance premise is supplied. -/
theorem adaptive_uniform_invariant (i : Fin 881) (s : Finset (Fin 3)) (hs : Pruning i s)
    (z : ℂ) (hz : z ∈ ActivityTube) (m : Fin 3 → ℂ)
    (hm : ∀ d ∈ s, m d ∈ Omega (childType i d)) :
    adaptiveMap i s z m ∈ Omega i ∧
    (1/200:ℝ) ≤ (logArgument s (aa i) (bb i)
      (fun d => aa (childType i d)) (fun d => bb (childType i d)) z m).re ∧
    (1/2:ℝ) ≤ (1+z*messageProduct s
      (fun d => aa (childType i d)) (fun d => bb (childType i d)) m).re ∧
    (∑ d ∈ s, ‖jacobianEntry s (aa i) (bb i)
      (fun d => aa (childType i d)) (fun d => bb (childType i d)) z m d‖) < 1999/2000 := by
  obtain ⟨lam,hlam,hz⟩ := hz
  have hw : ∀ d : Fin 3, ∃ r:ℝ, r ∈ Set.Icc (20/71) 1 ∧
      (d ∈ s → ‖m d-center (aa (childType i d)) (bb (childType i d)) r‖ < delta) := by
    intro d
    by_cases hd : d ∈ s
    · obtain ⟨r,hr,hclose⟩ := hm d hd
      exact ⟨r,hr,fun _ => hclose⟩
    · exact ⟨1,by constructor <;> norm_num,fun h => False.elim (hd h)⟩
  choose r hr using hw
  have hc := fun d (_ : d ∈ s) => actual_coefficient_bounds (childType i d)
  have hr' := fun d (_ : d ∈ s) => (hr d).1
  have hm' := fun d hd => ((hr d).2 hd).le
  have hs4 : s.card ≤ 4 := (Finset.card_le_univ s).trans (by norm_num)
  have hr4 : ∀ d ∈ s, (1/4:ℝ) ≤ r d ∧ r d ≤ 1 := by
    intro d hd; exact ⟨by linarith [(hr d).1.1],(hr d).1.2⟩
  have hl3 : 0 ≤ lam ∧ lam ≤ 3 := ⟨hlam.1,by linarith [hlam.2]⟩
  have hreal := real_row i s hs r hr' lam hlam
  have hst := row_tube_stability s hs4 (aa i) (bb i)
    (fun d => aa (childType i d)) (fun d => bb (childType i d)) r
    (actual_coefficient_bounds i) hc hr4 lam hl3 hreal z hz.le m hm'
  have hbase := row_at_centers s (aa i) (bb i)
    (fun d => aa (childType i d)) (fun d => bb (childType i d)) r
    (actual_coefficient_bounds i) hc hr' lam hlam
  dsimp only at hbase
  rw [hbase.2] at hst
  have hbound := row_tube_bounds s hs4 (aa i) (bb i)
    (fun d => aa (childType i d)) (fun d => bb (childType i d))
    (actual_coefficient_bounds i) hc r hr4 lam hl3 z hz.le m hm'
  exact ⟨⟨_,hbase.1,hst⟩,hbound.2.1,hbound.2.2.1,
    jacobian_tube_sum s hs4 (aa i) (bb i)
      (fun d => aa (childType i d)) (fun d => bb (childType i d)) r
      (actual_coefficient_bounds i) hc hr4 lam hl3 hreal z hz.le m hm'⟩

/-- The principal logarithm is the true inverse throughout each constructed
message neighborhood. Imaginary phase wrapping is excluded by the actual width. -/
theorem omega_chart_inverse (i : Fin 881) (m : ℂ) (hm : m ∈ Omega i) :
    chart (aa i) (bb i) (inverse (aa i) (bb i) m) = m := by
  obtain ⟨r,hr,he⟩ := hm
  have hc := actual_coefficient_bounds i
  have hb : 0 < bb i := by linarith [hc.1,hc.2.1]
  have hd := (inverse_tube (aa i) (bb i) r hc.1 hc.2.1 hc.2.2
    ⟨by linarith [hr.1],hr.2⟩ m he.le).1
  have hh : ((bb i:ℂ)*m).im = ((bb i:ℂ)*(m-center (aa i) (bb i) r)).im := by
    simp [Complex.mul_im,center]
  have hn : ‖(bb i:ℂ)*(m-center (aa i) (bb i) r)‖ ≤ 3*delta := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb]
    exact mul_le_mul hc.2.2 he.le (norm_nonneg _) (by norm_num)
  have hi : |((bb i:ℂ)*m).im| ≤ 3*delta := by
    rw [hh]
    exact (Complex.abs_im_le_norm _).trans hn
  have hlo := (abs_le.mp hi).1
  have hhi := (abs_le.mp hi).2
  have hpi := Real.pi_gt_three
  have hw : 3*delta < (3:ℝ) := by norm_num [delta]
  exact chart_inverse (aa i) (bb i) m (by exact_mod_cast ne_of_gt hb) hd
    ⟨by linarith,by linarith⟩

/-- On the constructed neighborhood, the map is jointly holomorphic and its
inverse coordinate is exactly the hard-core vacancy, with both poles excluded. -/
theorem adaptive_holomorphic_recovery (i : Fin 881) (s : Finset (Fin 3)) (hs : Pruning i s)
    (z : ℂ) (hz : z ∈ ActivityTube) (m : Fin 3 → ℂ)
    (hm : ∀ d ∈ s, m d ∈ Omega (childType i d)) :
    DifferentiableAt ℂ (fun p : ℂ × (Fin 3 → ℂ) => adaptiveMap i s p.1 p.2) (z,m) ∧
    inverse (aa i) (bb i) (adaptiveMap i s z m) =
      (1+z*messageProduct s (fun d => aa (childType i d)) (fun d => bb (childType i d)) m)⁻¹ := by
  have hi := adaptive_uniform_invariant i s hs z hz m hm
  have hd (d) (hd : d ∈ s) :
      1+(aa (childType i d):ℂ)*Complex.exp ((bb (childType i d):ℂ)*m d) ≠ 0 := by
    obtain ⟨r,hr,hclose⟩ := hm d hd
    have c := actual_coefficient_bounds (childType i d)
    exact (inverse_tube _ _ _ c.1 c.2.1 c.2.2
      ⟨by linarith [hr.1],hr.2⟩ _ hclose.le).1
  have hslit := Complex.mem_slitPlane_iff.mpr
    (Or.inl (lt_of_lt_of_le (by norm_num) hi.2.1))
  have hD : 1+z*messageProduct s (fun d => (aa (childType i d):ℂ))
      (fun d => (bb (childType i d):ℂ)) m ≠ 0 := by
    intro h; have := hi.2.2.1; norm_num [h] at this
  have hb : (bb i:ℂ) ≠ 0 := by
    have c := actual_coefficient_bounds i
    have h : 0 < bb i := by linarith [c.1,c.2.1]
    exact_mod_cast ne_of_gt h
  exact ⟨rowMap_differentiableAt s (aa i) (bb i)
      (fun d => aa (childType i d)) (fun d => bb (childType i d)) (z,m) hd hslit,
    inverse_rowMap s (aa i) (bb i) (fun d => aa (childType i d))
      (fun d => bb (childType i d)) z m hb (Complex.slitPlane_ne_zero hslit) hD⟩

/-- Four root factors need nonvanishing, not a three-child contraction claim.
Every first child may use the already-owned initial type zero. -/
theorem four_child_root_nonzero (z : ℂ) (hz : z ∈ ActivityTube)
    (m : Fin 4 → ℂ) (hm : ∀ e, m e ∈ Omega 0) :
    (1/2:ℝ) ≤ (1+z*∏ e, inverse (aa 0) (bb 0) (m e)).re ∧
    1+z*∏ e, inverse (aa 0) (bb 0) (m e) ≠ 0 := by
  obtain ⟨lam,hlam,hz⟩ := hz
  choose r hr using hm
  have h := row_tube_bounds (Finset.univ : Finset (Fin 4)) (by norm_num)
    (aa 0) (bb 0) (fun _ => aa 0) (fun _ => bb 0)
    (actual_coefficient_bounds 0) (fun _ _ => actual_coefficient_bounds 0) r
    (fun e _ => ⟨by linarith [(hr e).1.1],(hr e).1.2⟩) lam
    ⟨hlam.1,by linarith [hlam.2]⟩ z hz.le m (fun e _ => (hr e).2.le)
  have hd : (1/2:ℝ) ≤ (1+z*∏ e, inverse (aa 0) (bb 0) (m e)).re := h.2.2.1
  refine ⟨hd, ?_⟩
  intro he; norm_num [he] at hd

#print axioms actual_coefficient_bounds
#print axioms neighborhoods_open
#print axioms adaptive_uniform_invariant
#print axioms omega_chart_inverse
#print axioms adaptive_holomorphic_recovery
#print axioms four_child_root_nonzero
end D5.S3.HardCoreHolomorphic.AdaptiveComplexNeighborhood
