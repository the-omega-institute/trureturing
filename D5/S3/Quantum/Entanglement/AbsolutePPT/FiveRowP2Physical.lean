/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Physical
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Physical scalar extraction and exact concentrated moments for P2. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Nineteen
import D5.S3.Quantum.Entanglement.AbsolutePPT.HalfspaceConeTransfer
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
import D5.S3.Quantum.Entanglement.AbsolutePPT.UniformSchmidtVarianceConsumer
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
set_option autoImplicit false
open Matrix Finset
open scoped ComplexOrder BigOperators
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift
open UniformSpectralBound.SharedSpectral
noncomputable section

def middle (N : ℕ) : Finset (Fin N) :=
  univ.filter (fun i => 9 ≤ i.val ∧ i.val < N-15)
def middleMass {N : ℕ} (g : Fin N → ℝ) : ℝ := ∑ i ∈ middle N, g i
def frozen {N : ℕ} (g : Fin N → ℝ) : Fin N → ℝ :=
  ∑ i ∈ univ.filter (fun i => i ∉ middle N), g i • step N (i.val+1)
def concentrated {N : ℕ} (g : Fin N → ℝ) (j : Fin N) : Fin N → ℝ :=
  frozen g+middleMass g • step N (j.val+1)

private theorem split_gaps {N : ℕ} (g : Fin N → ℝ) :
    frozen g+∑ i ∈ middle N, g i • step N (i.val+1) =
      ∑ i, g i • step N (i.val+1) := by
  classical
  have hs : (∑ i ∈ middle N, g i • step N (i.val+1)) =
      ∑ i, if i ∈ middle N then g i • step N (i.val+1) else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp
  rw [hs]
  simp only [frozen,Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ middle N <;> simp [hi]

/-- Reconstructed concentrated vectors remain nonnegative. This follows
from genuine nonnegative gaps, not from a target moment inequality. -/
theorem concentrated_nonnegative {N : ℕ} (l : Fin N → ℝ) (ho : Antitone l)
    (hn : ∀ i,0 ≤ l i) (j : Fin N) :
    ∀ k,0 ≤ concentrated (spectralGap l) j k := by
  have hg := spectralGap_nonneg l ho hn
  have hstep (i k : Fin N) : 0 ≤ step N (i.val+1) k := by
    unfold step
    split_ifs <;> norm_num
  intro k
  have hm : 0 ≤ middleMass (spectralGap l) := sum_nonneg (fun i _ => hg i)
  unfold concentrated frozen
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  exact add_nonneg (sum_nonneg (fun i _ => mul_nonneg (hg i) (hstep i k)))
    (mul_nonneg hm (hstep j k))

/-- The actual middle mass is lambda_10-lambda_(N-14) in one-based notation. -/
theorem middle_mass_actual {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) :
    middleMass (spectralGap l) = l ⟨9,by omega⟩-l ⟨N-15,by omega⟩ := by
  classical
  unfold middleMass middle
  simp only [Finset.sum_filter,spectralGap]
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ =>
    if 9 ≤ i ∧ i < N-15 then extend l i-extend l (i+1) else 0)]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero,add_zero]
  have hf : (range N).filter (fun i => 9 ≤ i ∧ i < N-15) = Ico 9 (N-15) := by
    ext i
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [hf,gap_telescope l 9 (N-15) (by omega)]
  simp [extend,show 9 < N by omega,show N-15 < N by omega]

/-- Every concentrated spectrum has EXACTLY the original top ten and bottom
fifteen labelled values. The middle values need not be equal in the input. -/
theorem concentrated_boundary {N : ℕ} (l : Fin N → ℝ) (j : Fin N)
    (hj : j ∈ middle N) (k : Fin N) (hk : k.val < 10 ∨ N-15 ≤ k.val) :
    concentrated (spectralGap l) j k = l k := by
  classical
  have hsplit := split_gaps (spectralGap l)
  rw [gap_reconstruct l] at hsplit
  have hstep (i : Fin N) (hi : i ∈ middle N) :
      step N (i.val+1) k = step N (j.val+1) k := by
    have hmi : 9 ≤ i.val ∧ i.val < N-15 := (mem_filter.mp hi).2
    have hmj : 9 ≤ j.val ∧ j.val < N-15 := (mem_filter.mp hj).2
    rcases hk with hk | hk
    · simp [step,show k.val < i.val+1 by omega,show k.val < j.val+1 by omega]
    · simp [step,show ¬ k.val < i.val+1 by omega,show ¬ k.val < j.val+1 by omega]
  have hsum : (∑ i ∈ middle N, spectralGap l i • step N (i.val+1)) k =
      middleMass (spectralGap l)*step N (j.val+1) k := by
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,middleMass]
    rw [Finset.sum_mul]
    exact sum_congr rfl (fun i hi => by rw [hstep i hi])
  have hv := congrFun hsplit k
  simpa [concentrated,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hsum] using hv

/-- Reuse the canonical norm cone; no equal-mass or squared-Jensen premise. -/
theorem concentration_transfer {N : ℕ} (hN : 25 ≤ N) (theta : ℝ) (ht : 0 ≤ theta)
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hc : ∀ j ∈ middle N,
      0 ≤ ∑ i, concentrated (spectralGap l) j i)
    (hb : ∀ j ∈ middle N,
      ∑ i, (concentrated (spectralGap l) j i)^2 ≤
        theta*(∑ i, concentrated (spectralGap l) j i)^2) :
    ∑ i, (l i)^2 ≤ theta*(∑ i, l i)^2 := by
  have hm : (middle N).Nonempty := by
    refine ⟨⟨9,by omega⟩,?_⟩
    simp [middle]
    omega
  have hg := spectralGap_nonneg l ho hn
  have hg0 : 0 ≤ middleMass (spectralGap l) := sum_nonneg (fun i _ => hg i)
  have hgood : spectralGood (Real.sqrt theta) l := by
    have hfixed (j : Fin N) (hj : j ∈ middle N) :
        spectralGood (Real.sqrt theta) (concentrated (spectralGap l) j) := by
      apply spectralGood_of_square _ _ (Real.sqrt_nonneg _) (hc j hj)
      simpa [Real.sq_sqrt ht] using hb j hj
    have hmix := mixture_transfer (spectralGood (Real.sqrt theta))
      (spectralGood_zero N _) (fun x y hx hy => spectralGood_add _ x y hx hy)
      (fun t x ht' hx => spectralGood_smul _ t x ht' hx)
      (middle N) hm (spectralGap l) (fun i => step N (i.val+1))
      (frozen (spectralGap l)) (fun i _ => hg i) hfixed
    rwa [split_gaps,gap_reconstruct] at hmix
  have h := spectralGood_square (Real.sqrt theta) l (Real.sqrt_nonneg _)
    (sum_nonneg (fun i _ => hn i)) hgood
  simpa [Real.sq_sqrt ht] using h

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Lift

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Physical
open UniformSchmidtSpectrum UniformSchmidtBell UniformSchmidtDefectMoment
open UniformSchmidtVarianceConsumer UniformSchmidtIncidence
open QutritPerturbationAttainment FiveRowP2Scalar FiveRowP2Nineteen FiveRowP2Lift
open UniformSpectralBound.SharedSpectral
noncomputable section

/-- A true literal APPT consumer. The SAME actual spectrum produces every K.
This does not reinterpret a supplied PSD family as physical input. -/
theorem literal_five_row_variance (n : ℕ) (hn : 5 ≤ n)
    (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ)
    (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    let hN : a 5+b 5 ≤ 5*n := (pool_card_sum 5).trans_le (Nat.mul_le_mul (by rfl) hn)
    let A := ∑ k : Fin (a 5),l (topIndex hN k)
    let B' := ∑ k : Fin (b 5),l (bottomIndex hN k)
    let s := B'-A
    let u := l (bottomStart hN (bottom_pos (by norm_num)))
    momentLHS hN l ≤ 4*u*s-(2/5)*s^2 := by
  dsimp only
  let hN : a 5+b 5 ≤ 5*n := (pool_card_sum 5).trans_le (Nat.mul_le_mul (by rfl) hn)
  let A := ∑ k : Fin (a 5),l (topIndex hN k)
  let B' := ∑ k : Fin (b 5),l (bottomIndex hN k)
  let s := B'-A
  let u := l (bottomStart hN (bottom_pos (by norm_num)))
  have hm := literal_variance_moment (by norm_num : 2 ≤ 5) (by rfl : 5 ≤ 5) hn e l hl h
  dsimp only [momentRHS] at hm
  have hK := literal_assignment_psd (by rfl : 5 ≤ 5) hn e l h (Equiv.refl _) (Equiv.refl _)
  dsimp only at hK
  have hq : 0 ≤ uniformCharge (assignedK hN l (Equiv.refl _) (Equiv.refl _)) := by
    simpa [uniformCharge,rowSum,dotProduct,mulVec] using
      hK.dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
  rw [assignedK_charge] at hq
  have hs : 0 ≤ s := by dsimp [s,A,B']; linarith only [hq]
  have hmin := mul_le_mul_of_nonneg_left
    (min_le_right (B'/6) u) (show 0 ≤ 4*s by positivity)
  change momentLHS hN l ≤ _
  norm_num only [Nat.cast_ofNat, show (5:ℝ)+1=6 by norm_num] at hm
  change momentLHS hN l ≤ 4*s*min (B'/6) u-2*s^2/5 at hm
  nlinarith only [hm,hmin]

/-- Precise zero-based boundary data of the unchanged ordered spectrum. -/
def u {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ := l ⟨N-15,by omega⟩
def v {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ := l ⟨9,by omega⟩-u hN l
def heads {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : Fin 10 → ℝ :=
  fun i => l ⟨i.val,by omega⟩-l ⟨9,by omega⟩
def tails {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : Fin 15 → ℝ :=
  fun i => u hN l-l ⟨N-15+i.val,by omega⟩
def H {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ := ∑ i,heads hN l i
def D {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ := ∑ i,tails hN l i
def headEnergy {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ := ∑ i,(heads hN l i)^2
def tailEnergy {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : ℝ := ∑ i,(tails hN l i)^2

/-- Literal Bell compression supplies EVERY independent labelled K5
assignment of these exact head and tail defects. -/
theorem literal_defect_family (n : ℕ) (hn : 5 ≤ n)
    (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    let hN : 25 ≤ 5*n := by omega
    FiveRowP2Star.FullPSD (u hN l) (v hN l) (heads hN l) (tails hN l) := by
  dsimp only
  let hN : 25 ≤ 5*n := by omega
  have ha : a 5=10 := by
    have hc := edge_card_real 5
    norm_num at hc
    exact_mod_cast hc
  have hb : b 5=15 := by
    have hc := bottom_card_real 5
    norm_num at hc
    exact_mod_cast hc
  let hpool : a 5+b 5 ≤ 5*n := (pool_card_sum 5).trans_le (Nat.mul_le_mul (by rfl) hn)
  intro π σ
  let π' : Equiv.Perm (Fin (a 5)) :=
    (Fintype.equivFin (Edge 5)).symm.trans (π.trans (finCongr ha).symm)
  let σ' : Equiv.Perm (Fin (b 5)) :=
    (Fintype.equivFin (BottomSlot 5)).symm.trans (σ.trans (finCongr hb).symm)
  have hpsd := literal_assignment_psd (by rfl : 5 ≤ 5) hn e l h π' σ'
  dsimp only at hpsd
  have htop (z : Edge 5) : u hN l+v hN l+heads hN l (π z)=
      l (assignedTopIndex hpool π' z) := by
    have hi : assignedTopIndex hpool π' z=⟨(π z).val,by omega⟩ := by
      apply Fin.ext
      simp [assignedTopIndex,topIndex,π',Equiv.trans_apply]
    rw [hi]
    dsimp [v,heads]
    ring
  have hbot (z : BottomSlot 5) : u hN l-tails hN l (σ z)=
      l (assignedBottomIndex hpool σ' z) := by
    have hi : assignedBottomIndex hpool σ' z=⟨5*n-15+(σ z).val,by omega⟩ := by
      apply Fin.ext
      simp [assignedBottomIndex,bottomIndex,σ',Equiv.trans_apply,hb]
    rw [hi]
    dsimp [tails]
    ring
  have hid : FiveRowP2Star.family (u hN l) (v hN l) (heads hN l) (tails hN l) π σ =
      assignedK hpool l π' σ' := by
    unfold FiveRowP2Star.family assignedK
    congr 1 <;> funext z
    · exact htop z
    · exact hbot z
  rwa [hid]

/-- Ordering and nonnegativity yield the actual pool signs and tail box;
head slot 9 and tail slot 0 are zero by definition, even at ties. -/
theorem actual_pool_signs {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ)
    (hl : Antitone l) (h0 : ∀ i,0 ≤ l i) :
    0 ≤ u hN l ∧ 0 ≤ v hN l ∧ (∀ i,0 ≤ heads hN l i) ∧
      (∀ i,0 ≤ tails hN l i ∧ tails hN l i ≤ u hN l) ∧
      heads hN l 9=0 ∧ tails hN l 0=0 := by
  refine ⟨h0 _,?_,?_,?_,?_,?_⟩
  · exact sub_nonneg.mpr (hl (by change 9 ≤ N-15; omega))
  · intro i
    exact sub_nonneg.mpr (hl (by change i.val ≤ 9; omega))
  · intro i
    constructor
    · exact sub_nonneg.mpr (hl (by change N-15 ≤ N-15+i.val; omega))
    · dsimp [tails]
      linarith [h0 ⟨N-15+i.val,by omega⟩]
  · simp [heads]
  · simp [tails,u]

/-- Homogeneous zero-u and hence zero-S spectra are retained, before division. -/
theorem homogeneous_zero_actual (n : ℕ) (hn : 5 ≤ n)
    (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ)
    (hl : Antitone l) (h0 : ∀ i,0 ≤ l i)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ))))
    (hu : u (by omega : 25 ≤ 5*n) l=0) : l=0 := by
  let hN : 25 ≤ 5*n := by omega
  have hs := actual_pool_signs hN l hl h0
  have hf := literal_defect_family n hn e l h
  dsimp only at hf
  have hb := FiveRowP2Star.family_mass_budget (u hN l) (v hN l) (heads hN l) (tails hN l) hf
  have hH0 : 0 ≤ ∑ i,heads hN l i := sum_nonneg (fun i _ => hs.2.2.1 i)
  have hD0 : 0 ≤ ∑ i,tails hN l i := sum_nonneg (fun i _ => (hs.2.2.2.1 i).1)
  have hHz : (∑ i,heads hN l i)=0 := by nlinarith [hs.2.1]
  have hvz : v hN l=0 := by nlinarith [hs.2.1]
  have hh := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (univ : Finset (Fin 10))) =>
    hs.2.2.1 i)).mp hHz 0 (mem_univ _)
  have hl9 : l ⟨9,by omega⟩=0 := by dsimp [v] at hvz; linarith
  have hl0 : l ⟨0,by omega⟩=0 := by simpa [heads,hl9] using hh
  funext i
  have ho : l i ≤ l ⟨0,by omega⟩ := hl (by change 0 ≤ i.val; omega)
  exact le_antisymm (by simpa [hl0] using ho) (h0 i)

def normalizedHyp {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) : Prop :=
  Hyp (v hN l/u hN l) (H hN l/u hN l) (D hN l/u hN l)
    (headEnergy hN l/(u hN l)^2) (tailEnergy hN l/(u hN l)^2)
    ((5*u hN l-10*v hN l-H hN l-D hN l)/u hN l)

/-- Exact physical scalar extraction telescope, preserved independently of its
proof. There is no target-purity bound in its conclusion. -/
def PhysicalScalarExtractionGap : Prop :=
  ∀ (n : ℕ) (hn : 19 ≤ n) (e : (Fin 5 × Fin n) ≃ Fin (5*n))
    (l : Fin (5*n) → ℝ), Antitone l → (∀ i,0 ≤ l i) →
    APPT (diagonal (fun p => (l (e p) : ℂ))) →
    let hN : 25 ≤ 5*n := by omega
    0 < u hN l → normalizedHyp hN l

/-- Exact arbitrary-real moment telescope, including original scale and mass. -/
def ConcentratedMomentsGap : Prop :=
  ∀ (N : ℕ) (hN : 25 ≤ N) (l : Fin N → ℝ) (j : Fin N),
    j ∈ middle N → 0 < u hN l →
    let r := v hN l/u hN l
    let HH := H hN l/u hN l
    let DD := D hN l/u hN l
    let aa := headEnergy hN l/(u hN l)^2
    let qq := tailEnergy hN l/(u hN l)^2
    ((∑ i,concentrated (UniformSpectralBound.SharedSpectral.spectralGap l) j i)=
      u hN l*mass N (j.val+1) r HH DD) ∧
    ((∑ i,(concentrated (UniformSpectralBound.SharedSpectral.spectralGap l) j i)^2)=
      (u hN l)^2*energy N (j.val+1) r HH DD aa qq)

private theorem five_edge_card : a 5=10 := by
  have hc := edge_card_real 5
  norm_num at hc
  exact_mod_cast hc

private theorem five_bottom_card : b 5=15 := by
  have hc := bottom_card_real 5
  norm_num at hc
  exact_mod_cast hc

/-- Cauchy on the complement of the actual zero slot. -/
theorem zero_slot_cauchy {m : ℕ} (z : Fin (m+1) → ℝ)
    (i : Fin (m+1)) (hi : z i=0) :
    (∑ j,z j)^2 ≤ (m:ℝ)*(∑ j,(z j)^2) := by
  classical
  have hs : (∑ j ∈ univ.erase i,z j)=∑ j,z j := by
    simpa [hi] using sum_erase_add univ z (mem_univ i)
  have hq : (∑ j ∈ univ.erase i,(z j)^2)=∑ j,(z j)^2 := by
    simpa [hi] using sum_erase_add univ (fun j => (z j)^2) (mem_univ i)
  have hc := sum_mul_sq_le_sq_mul_sq (univ.erase i) z (fun _ => (1:ℝ))
  have hcard : (univ.erase i).card=m := by simp
  simpa [mul_one,hs,hq,hcard,mul_comm] using hc

/-- Singular-safe two-coordinate Cauchy, derived from the PSD bilinear form. -/
private theorem psd_entry_square (M : Matrix (Fin 5) (Fin 5) ℝ)
    (hM : M.PosSemidef) (i j : Fin 5) : (M i j)^2 ≤ M i i*M j j := by
  let B : LinearMap.BilinForm ℝ (Fin 5 → ℝ) := Matrix.toLinearMap₂' ℝ M
  have hp : ∀ x,0 ≤ B x x := by
    intro x
    simpa [B,Matrix.toLinearMap₂'_apply'] using hM.dotProduct_mulVec_nonneg x
  have hs : LinearMap.IsSymm B := by
    constructor
    intro x y
    simpa [B,Matrix.toLinearMap₂'_apply'] using
      hM.isHermitian.star_dotProduct_mulVec_comm x y
  have hcs := B.apply_sq_le_of_symm hp hs (Pi.single i 1) (Pi.single j 1)
  simpa [B,Matrix.toLinearMap₂'_apply',dotProduct,mulVec,Pi.single_apply] using hcs

/-- An explicit labelled placement: 14 and 13 are diagonal slots, and 12
is their connecting edge. All remaining labels are assigned bijectively. -/
private def tailPlacement : BottomSlot 5 → Fin 15
  | .inl i => ![14,13,0,1,2] i
  | .inr e =>
    if e.val.1=0 then ![0,12,3,4,5] e.val.2
    else if e.val.1=1 then ![0,0,6,7,8] e.val.2
    else if e.val.1=2 then ![0,0,0,9,10] e.val.2
    else 11

private def tailEquiv : BottomSlot 5 ≃ Fin 15 :=
  Equiv.ofBijective tailPlacement (by decide)

/-- Top-three tail constraint from the exact two diagonals and third
connecting edge, with an independent head assignment. -/
theorem top_three_psd (U V : ℝ) (h : Fin 10 → ℝ) (d : Fin 15 → ℝ)
    (hV : 0 ≤ V) (hh : ∀ i,0 ≤ h i) (hd : ∀ i,0 ≤ d i)
    (hf : FiveRowP2Star.FullPSD U V h d) :
    (d 12)^2 ≤ 4*(U-d 14)*(U-d 13) := by
  let π : Edge 5 ≃ Fin 10 :=
    (Fintype.equivFin (Edge 5)).trans (finCongr five_edge_card)
  let e01 : Edge 5 := ⟨(0,1),by decide⟩
  have hcs := psd_entry_square (FiveRowP2Star.family U V h d π tailEquiv)
    (hf π tailEquiv) 0 1
  have h00 : FiveRowP2Star.family U V h d π tailEquiv 0 0=2*(U-d 14) := by
    norm_num [FiveRowP2Star.family,K,tailEquiv,tailPlacement]
  have h11 : FiveRowP2Star.family U V h d π tailEquiv 1 1=2*(U-d 13) := by
    norm_num [FiveRowP2Star.family,K,tailEquiv,tailPlacement]
  have h01 : FiveRowP2Star.family U V h d π tailEquiv 0 1=
      -(V+h (π e01)+d 12) := by
    simp [FiveRowP2Star.family,K,edge,e01,tailEquiv,tailPlacement]
    ring
  rw [h00,h11,h01] at hcs
  have hx : 0 ≤ V+h (π e01) := add_nonneg hV (hh _)
  have hp := mul_nonneg hx (show 0 ≤ V+h (π e01)+2*d 12 by linarith [hd 12])
  nlinarith only [hcs,hp]

/-- Tail-square factorization for a monotone unit-box list and any mass
budget m>=3. No division by an entry, gap, or principal minor occurs. -/
theorem monotone_tail_square_cap (z : Fin 15 → ℝ) (m : ℝ)
    (hm : 3 ≤ m) (h0 : ∀ i,0 ≤ z i) (h1 : ∀ i,z i ≤ 1)
    (ho : Monotone z) (hsum : ∑ i,z i ≤ m)
    (hp : (z 12)^2 ≤ 4*(1-z 14)*(1-z 13)) :
    (∑ i,(z i)^2) ≤ 2*m/3 := by
  let a := z 14
  let b := z 13
  let c := z 12
  have ha0 : 0 ≤ a := h0 14
  have hb0 : 0 ≤ b := h0 13
  have hc0 : 0 ≤ c := h0 12
  have ha1 : a ≤ 1 := h1 14
  have hb1 : b ≤ 1 := h1 13
  have hca : c ≤ a := ho (by decide : (12:Fin 15) ≤ 14)
  have hcb : c ≤ b := ho (by decide : (12:Fin 15) ≤ 13)
  change c^2 ≤ 4*(1-a)*(1-b) at hp
  have hcs : c ≤ 2-a-b := by
    have hsq : c^2 ≤ (2-a-b)^2 := by nlinarith only [hp,sq_nonneg (a-b)]
    exact (sq_le_sq₀ hc0 (by linarith)).mp hsq
  have hcu : c ≤ 2/3 := by linarith
  have he := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (2-a-b)-c by linarith)
    (show (2-a-b)-(2-2*c) ≤ 0 by linarith)
  have hab : a^2+b^2-c*(a+b) ≤ 2-4*c+3*c^2/2 := by
    nlinarith only [hp,he]
  have hpoint (i : Fin 15) : (z i)^2 ≤ c*z i+
      (if i=14 then a^2-c*a else 0)+(if i=13 then b^2-c*b else 0) := by
    by_cases hi : i=14
    · subst i
      simp only [if_pos rfl,if_neg (by decide : (14:Fin 15) ≠ 13)]
      dsimp [a]
      nlinarith only []
    · by_cases hi' : i=13
      · subst i
        simp only [if_neg (by decide : (13:Fin 15) ≠ 14),if_pos rfl]
        dsimp [b]
        nlinarith only []
      · have hic : z i ≤ c := ho (by change i.val ≤ 12; omega)
        have hi0 := mul_nonneg (h0 i) (sub_nonneg.mpr hic)
        simp only [if_neg hi,if_neg hi']
        nlinarith only [hi0]
  have hsq := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 15))) => hpoint i)
  simp only [sum_add_distrib,← mul_sum] at hsq
  simp only [sum_ite_eq',mem_univ,if_true] at hsq
  have hmass := mul_le_mul_of_nonneg_left hsum hc0
  have hfac := mul_nonneg (show 0 ≤ 2/3-c by linarith)
    (show 0 ≤ m-3+3*c/2 by linarith)
  nlinarith only [hsq,hmass,hab,hfac]

private theorem actual_tail_cap (n : ℕ) (hn : 19 ≤ n)
    (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ)
    (hl : Antitone l) (h0 : ∀ i,0 ≤ l i)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ))))
    (hu : 0 < u (by omega : 25 ≤ 5*n) l) :
    tailEnergy (by omega : 25 ≤ 5*n) l/(u (by omega) l)^2 ≤ 10/3 := by
  let hN : 25 ≤ 5*n := by omega
  let U := u hN l
  let z : Fin 15 → ℝ := fun i => tails hN l i/U
  have hs := actual_pool_signs hN l hl h0
  have hf := literal_defect_family n (by omega) e l h
  dsimp only at hf
  have hb := FiveRowP2Star.family_mass_budget _ _ _ _ hf
  have hH : 0 ≤ H hN l := sum_nonneg (fun i _ => hs.2.2.1 i)
  have hD : D hN l ≤ 5*U := by change H hN l+D hN l ≤ _ at hb; nlinarith [hs.2.1]
  have hsum : ∑ i,z i ≤ 5 := by
    simp only [z,← sum_div]
    exact (div_le_iff₀ hu).mpr (by simpa [D,U] using hD)
  have hz0 (i : Fin 15) : 0 ≤ z i := div_nonneg (hs.2.2.2.1 i).1 hu.le
  have hz1 (i : Fin 15) : z i ≤ 1 :=
    (div_le_one hu).mpr (hs.2.2.2.1 i).2
  have hzo : Monotone z := by
    intro i j hij
    apply (div_le_div_iff_of_pos_right hu).mpr
    have ho := hl (show (⟨5*n-15+i.val,by omega⟩ : Fin (5*n)) ≤
      ⟨5*n-15+j.val,by omega⟩ by exact Nat.add_le_add_left hij _)
    dsimp [tails]
    linarith
  have hp := top_three_psd U (v hN l) (heads hN l) (tails hN l)
    hs.2.1 hs.2.2.1 (fun i => (hs.2.2.2.1 i).1) hf
  have hU : U ≠ 0 := ne_of_gt hu
  have hpz : (z 12)^2 ≤ 4*(1-z 14)*(1-z 13) := by
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hu)).mp
    have hid : U^2*((z 12)^2)=(tails hN l 12)^2 := by
      dsimp [z]
      field_simp [hU] <;> ring
    have hid' : U^2*(4*(1-z 14)*(1-z 13))=
        4*(U-tails hN l 14)*(U-tails hN l 13) := by
      dsimp [z]
      field_simp [hU]
      <;> ring
    rwa [hid,hid']
  have hz := monotone_tail_square_cap z 5 (by norm_num) hz0 hz1 hzo hsum hpz
  have hid : (∑ i,(z i)^2)=tailEnergy hN l/U^2 := by
    simp [z,div_pow,← sum_div,tailEnergy]
  rw [hid] at hz
  norm_num only at hz
  simpa only [U] using hz

private theorem top_pool_sum {N : ℕ} (hN : 25 ≤ N)
    (hp : a 5+b 5 ≤ N) (l : Fin N → ℝ) (F : ℝ → ℝ) :
    (∑ k : Fin (a 5),F (l (topIndex hp k)))=
      ∑ i : Fin 10,F (u hN l+v hN l+heads hN l i) := by
  calc
    _ = ∑ k : Fin (a 5),F (u hN l+v hN l+heads hN l (finCongr five_edge_card k)) := by
      apply sum_congr rfl
      intro k _
      congr 1
      dsimp [u,v,heads,topIndex]
      ring
    _ = _ := Equiv.sum_comp (finCongr five_edge_card)
      (fun i : Fin 10 => F (u hN l+v hN l+heads hN l i))

private theorem bottom_pool_sum {N : ℕ} (hN : 25 ≤ N)
    (hp : a 5+b 5 ≤ N) (l : Fin N → ℝ) (F : ℝ → ℝ) :
    (∑ k : Fin (b 5),F (l (bottomIndex hp k)))=
      ∑ i : Fin 15,F (u hN l-tails hN l i) := by
  calc
    _ = ∑ k : Fin (b 5),F (u hN l-tails hN l (finCongr five_bottom_card k)) := by
      apply sum_congr rfl
      intro k _
      congr 1
      have hi : bottomIndex hp k=
          (⟨N-15+(finCongr five_bottom_card k).val,by omega⟩ : Fin N) := by
        apply Fin.ext
        change N-b 5+k.val = N-15+k.val
        exact congrArg (fun t : ℕ => N-t+k.val) five_bottom_card
      rw [hi]
      dsimp [tails]
      ring
    _ = _ := Equiv.sum_comp (finCongr five_bottom_card)
      (fun i : Fin 15 => F (u hN l-tails hN l i))

private theorem variance_expansion {k : ℕ} (hk : (k:ℝ) ≠ 0) (z : Fin k → ℝ) :
    variance z=(∑ i,(z i)^2)-(∑ i,z i)^2/(k:ℝ) := by
  unfold variance
  calc
    _ = ∑ i,((z i)^2-2*((∑ j,z j)/(k:ℝ))*z i+((∑ j,z j)/(k:ℝ))^2) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = (∑ i,(z i)^2)-2*((∑ j,z j)/(k:ℝ))*(∑ i,z i)+
        (k:ℝ)*((∑ j,z j)/(k:ℝ))^2 := by
      simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,
        card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ = _ := by field_simp [hk] <;> ring

/-- Centering uses the actual literal pools, with no supplied variance
or target-purity premise. -/
theorem actual_variance (n : ℕ) (hn : 5 ≤ n)
    (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ)
    (hl : Antitone l) (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    let hN : 25 ≤ 5*n := by omega
    let S := 5*u hN l-10*v hN l-H hN l-D hN l
    (2/3)*(headEnergy hN l-(H hN l)^2/10)+
      (tailEnergy hN l-(D hN l)^2/15) ≤ 4*u hN l*S-(2/5)*S^2 := by
  dsimp only
  let hN : 25 ≤ 5*n := by omega
  let hp : a 5+b 5 ≤ 5*n := by rw [five_edge_card,five_bottom_card]; omega
  have ht : (∑ k : Fin (a 5),l (topIndex hp k))=
      10*(u hN l+v hN l)+H hN l := by
    rw [top_pool_sum hN hp l (fun x => x)]
    simp [sum_add_distrib,H]
    ring
  have hb : (∑ k : Fin (b 5),l (bottomIndex hp k))=15*u hN l-D hN l := by
    rw [bottom_pool_sum hN hp l (fun x => x)]
    simp [sum_sub_distrib,D]
  have ht2 : (∑ k : Fin (a 5),(l (topIndex hp k))^2)=
      10*(u hN l+v hN l)^2+2*(u hN l+v hN l)*H hN l+headEnergy hN l := by
    rw [top_pool_sum hN hp l (fun x => x^2)]
    simp_rw [add_sq]
    simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,
      nsmul_eq_mul,H,headEnergy]
    ring
  have hb2 : (∑ k : Fin (b 5),(l (bottomIndex hp k))^2)=
      15*(u hN l)^2-2*u hN l*D hN l+tailEnergy hN l := by
    rw [bottom_pool_sum hN hp l (fun x => x^2)]
    simp_rw [sub_sq]
    simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,D,tailEnergy]
    norm_num
    <;> ring
  have hleft : momentLHS hp l=
      (2/3)*(headEnergy hN l-(H hN l)^2/10)+
        (tailEnergy hN l-(D hN l)^2/15) := by
    unfold momentLHS
    rw [variance_expansion (k := a 5) (by rw [five_edge_card]; norm_num)
        (fun k => l (topIndex hp k)),
      variance_expansion (k := b 5) (by rw [five_bottom_card]; norm_num)
        (fun k => l (bottomIndex hp k)),ht,hb,ht2,hb2]
    norm_num only [five_edge_card,five_bottom_card]
    ring
  have hu : l (bottomStart hp (bottom_pos (by norm_num : 2 ≤ 5)))=u hN l := by
    change l (bottomStart hp (bottom_pos (by norm_num : 2 ≤ 5)))=
      l ⟨5*n-15,by omega⟩
    congr 1
  have hv := literal_five_row_variance n (by omega) e l hl h
  dsimp only at hv
  change momentLHS hp l ≤
    4*l (bottomStart hp (bottom_pos (by norm_num : 2 ≤ 5)))*
      ((∑ k : Fin (b 5),l (bottomIndex hp k))-(∑ k : Fin (a 5),l (topIndex hp k)))-
      (2/5)*((∑ k : Fin (b 5),l (bottomIndex hp k))-
        (∑ k : Fin (a 5),l (topIndex hp k)))^2 at hv
  rw [hleft,ht,hb,hu] at hv
  convert hv using 1 <;> ring

/-- Genuine modular extraction: a balanced-star witness is the finite
construction input. Every scalar field is then derived from the actual pools. -/
theorem physical_extraction_with_witness (n : ℕ) (hn : 19 ≤ n)
    (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ)
    (hl : Antitone l) (h0 : ∀ i,0 ≤ l i)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ))))
    (hu : 0 < u (by omega : 25 ≤ 5*n) l)
    (w : FiveRowP2Star.CouplingWitness (u (by omega) l) (v (by omega) l)
      (heads (by omega) l) (tails (by omega) l)) :
    normalizedHyp (by omega) l := by
  let hN : 25 ≤ 5*n := by omega
  let U := u hN l
  let V := v hN l
  let HH := H hN l
  let DD := D hN l
  let A := headEnergy hN l
  let Q := tailEnergy hN l
  let S := 5*U-10*V-HH-DD
  have hs := actual_pool_signs hN l hl h0
  have hV : 0 ≤ V := hs.2.1
  have hH : 0 ≤ HH := sum_nonneg (fun i _ => hs.2.2.1 i)
  have hD : 0 ≤ DD := sum_nonneg (fun i _ => (hs.2.2.2.1 i).1)
  have hA : 0 ≤ A := sum_nonneg (fun i _ => sq_nonneg _)
  have hQ : 0 ≤ Q := sum_nonneg (fun i _ => sq_nonneg _)
  have hf := literal_defect_family n (by omega) e l h
  dsimp only at hf
  have hb := FiveRowP2Star.family_mass_budget _ _ _ _ hf
  change HH+DD ≤ 5*U-10*V at hb
  have hS : 0 ≤ S := by dsimp [S]; linarith
  have hr : V/U ≤ 1/2 := (div_le_iff₀ hu).mpr (by linarith)
  have hamin : HH^2 ≤ 9*A := zero_slot_cauchy (heads hN l) 9 hs.2.2.2.2.1
  have hqmin : DD^2 ≤ 14*Q := zero_slot_cauchy (tails hN l) 0 hs.2.2.2.2.2
  have hamax : A ≤ HH^2 := sum_sq_le_sq_sum_of_nonneg (fun i _ => hs.2.2.1 i)
  have hqmass : Q ≤ DD^2 := sum_sq_le_sq_sum_of_nonneg (fun i _ => (hs.2.2.2.1 i).1)
  have hqbox : Q ≤ U*DD := by
    have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 15))) =>
      show (tails hN l i)^2 ≤ U*tails hN l i by
        have hp := mul_nonneg (hs.2.2.2.1 i).1
          (sub_nonneg.mpr (hs.2.2.2.1 i).2)
        nlinarith only [hp])
    simpa only [← mul_sum,Q,DD,tailEnergy,D] using hh
  have hqc : Q/U^2 ≤ 10/3 := actual_tail_cap n hn e l hl h0 h hu
  have hc := FiveRowP2Star.same_vector_coupling U V (heads hN l) (tails hN l) hf w
  have hroot : (∑ i,(V+heads hN l i)^2)=A+2*V*HH+10*V^2 := by
    simp_rw [add_sq]
    simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,
      nsmul_eq_mul,A,HH,H,headEnergy]
    ring
  rw [hroot] at hc
  change Real.sqrt (A+2*V*HH+10*V^2)+Q/(2*U) ≤ 2*U at hc
  have hrhs : 0 ≤ 2*U-Q/(2*U) := by linarith [Real.sqrt_nonneg (A+2*V*HH+10*V^2)]
  have hroot0 : 0 ≤ A+2*V*HH+10*V^2 := by positivity
  have hcoupled : A+2*V*HH+10*V^2 ≤ (2*U-Q/(2*U))^2 := by
    have hle : Real.sqrt (A+2*V*HH+10*V^2) ≤ 2*U-Q/(2*U) := by linarith
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hrhs).mpr hle
    rwa [Real.sq_sqrt hroot0] at hsq
  have hv := actual_variance n (by omega) e l hl h
  dsimp only at hv
  change (2/3)*(A-HH^2/10)+(Q-DD^2/15) ≤ 4*U*S-(2/5)*S^2 at hv
  have hU : U ≠ 0 := ne_of_gt hu
  have hU2 : 0 < U^2 := sq_pos_of_pos hu
  have hnormH : (HH/U)^2=HH^2/U^2 := div_pow _ _ _
  have hnormD : (DD/U)^2=DD^2/U^2 := div_pow _ _ _
  have hcscale : (A/U^2+2*(V/U)*(HH/U)+10*(V/U)^2)*U^2=
      A+2*V*HH+10*V^2 := by field_simp [hU] <;> ring
  have hrscale : (2-Q/U^2/2)^2*U^2=(2*U-Q/(2*U))^2 := by
    field_simp [hU] <;> ring
  have hvscale : ((2/3)*(A/U^2-(HH/U)^2/10)+(Q/U^2-(DD/U)^2/15))*U^2=
      (2/3)*(A-HH^2/10)+(Q-DD^2/15) := by field_simp [hU] <;> ring
  have hvs : (4*(S/U)-(2/5)*(S/U)^2)*U^2=4*U*S-(2/5)*S^2 := by
    field_simp [hU] <;> ring
  change Hyp (V/U) (HH/U) (DD/U) (A/U^2) (Q/U^2) (S/U)
  refine ⟨div_nonneg hV hu.le,hr,div_nonneg hH hu.le,div_nonneg hD hu.le,
    div_nonneg hA hU2.le,div_nonneg hQ hU2.le,div_nonneg hS hu.le,?_,?_,?_,?_,?_,?_,hqc,?_,?_⟩
  · dsimp [S]
    field_simp [hU] <;> ring
  · rw [hnormH]
    apply (le_div_iff₀ hU2).mpr
    have hid : HH^2/U^2/9*U^2=HH^2/9 := by field_simp [hU] <;> ring
    rw [hid]
    linarith
  · rw [hnormH]
    exact (div_le_div_iff_of_pos_right hU2).mpr hamax
  · rw [hnormD]
    apply (le_div_iff₀ hU2).mpr
    have hid : DD^2/U^2/14*U^2=DD^2/14 := by field_simp [hU] <;> ring
    rw [hid]
    linarith
  · apply (div_le_iff₀ hU2).mpr
    have hid : DD/U*U^2=U*DD := by field_simp [hU] <;> ring
    rwa [hid]
  · rw [hnormD]
    exact (div_le_div_iff_of_pos_right hU2).mpr hqmass
  · apply (mul_le_mul_iff_of_pos_right hU2).mp
    rwa [hcscale,hrscale]
  · apply (mul_le_mul_iff_of_pos_right hU2).mp
    rwa [hvscale,hvs]

/-- The balanced-star construction supplies the same-vector coupling witness
for the literal head and tail pools, yielding all normalized scalar constraints. -/
theorem physicalScalarExtraction : PhysicalScalarExtractionGap := by
  intro n hn e l hl h0 h
  dsimp only
  intro hu
  let hN : 25 ≤ 5*n := by omega
  have hs := actual_pool_signs hN l hl h0
  have hf := literal_defect_family n (by omega) e l h
  dsimp only at hf
  have hb := FiveRowP2Star.family_mass_budget _ _ _ _ hf
  have hH : 0 ≤ H hN l := sum_nonneg (fun i _ => hs.2.2.1 i)
  have hD : D hN l ≤ 5*u hN l := by
    change H hN l+D hN l ≤ _ at hb
    nlinarith [hs.2.1]
  obtain ⟨w⟩ := FiveRowP2Star.balancedStarExistence (u hN l) (v hN l)
    (heads hN l) (tails hN l) hu hs.2.1 hs.2.2.1
    (fun i => (hs.2.2.2.1 i).1) (fun i => (hs.2.2.2.1 i).2) hD hf
  exact physical_extraction_with_witness n hn e l hl h0 h hu w

/-- The middle part removed from reconstruction, evaluated at an interior
coordinate. Only the canonical real-valued telescope is used. -/
private theorem middle_contribution {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ)
    (k : Fin N) (hk : 10 ≤ k.val ∧ k.val < N-15) :
    (∑ i ∈ middle N, spectralGap l i • step N (i.val+1)) k = l k-u hN l := by
  classical
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,middle,Finset.sum_filter]
  have he (i : Fin N) :
      (if 9 ≤ i.val ∧ i.val < N-15 then
        spectralGap l i*step N (i.val+1) k else 0) =
      (if k.val ≤ i.val ∧ i.val < N-15 then
        extend l i.val-extend l (i.val+1) else 0) := by
    by_cases hi : k.val ≤ i.val ∧ i.val < N-15
    · have hm : 9 ≤ i.val ∧ i.val < N-15 := by omega
      simp only [if_pos hi,if_pos hm,spectralGap,step,
        if_pos (show k.val < i.val+1 by omega)]
      ring
    · by_cases hm : 9 ≤ i.val ∧ i.val < N-15
      · simp only [if_neg hi,if_pos hm,step,
          if_neg (show ¬ k.val < i.val+1 by omega),mul_zero]
      · simp only [if_neg hi,if_neg hm]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ =>
    if k.val ≤ i ∧ i < N-15 then extend l i-extend l (i+1) else 0)]
  rw [sum_ite]
  simp only [sum_const_zero,add_zero]
  have hf : (range N).filter (fun i => k.val ≤ i ∧ i < N-15) =
      Ico k.val (N-15) := by
    ext i
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [hf,gap_telescope l k.val (N-15) (by omega)]
  simp [extend,u,k.isLt,show N-15 < N by omega]

private theorem reconstruction_split {N : ℕ} (l : Fin N → ℝ) :
    frozen (spectralGap l)+∑ i ∈ middle N,spectralGap l i • step N (i.val+1)=l := by
  classical
  have hmiddle : (∑ i ∈ middle N,spectralGap l i • step N (i.val+1)) =
      ∑ i, if i ∈ middle N then spectralGap l i • step N (i.val+1) else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp
  calc
    _ = ∑ i,spectralGap l i • step N (i.val+1) := by
      rw [hmiddle]
      simp only [frozen,Finset.sum_filter]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i _
      by_cases hi : i ∈ middle N <;> simp [hi]
    _ = l := gap_reconstruct l

/-- Exact interior value for arbitrary real input; order is unnecessary. -/
private theorem concentrated_interior {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ)
    (j k : Fin N) (hk : 10 ≤ k.val ∧ k.val < N-15) :
    concentrated (spectralGap l) j k =
      u hN l+v hN l*step N (j.val+1) k := by
  have hs := congrFun (reconstruction_split l) k
  have hm := middle_contribution hN l k hk
  have hv : middleMass (spectralGap l)=v hN l := by
    simpa [v,u] using middle_mass_actual hN l
  change frozen (spectralGap l) k+
    (∑ i ∈ middle N,spectralGap l i • step N (i.val+1)) k=l k at hs
  have hf : frozen (spectralGap l) k=u hN l := by linarith
  simp [concentrated,hv,hf]

private def headPad {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) (k : Fin N) : ℝ :=
  if hk : k.val < 10 then heads hN l ⟨k.val,hk⟩ else 0
private def tailPad {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ) (k : Fin N) : ℝ :=
  if hk : N-15 ≤ k.val then tails hN l ⟨k.val-(N-15),by omega⟩ else 0

private theorem headPad_sum {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ)
    (F : ℝ → ℝ) (hF : F 0=0) :
    (∑ k,F (headPad hN l k))=∑ i : Fin 10,F (heads hN l i) := by
  classical
  calc
    _ = ∑ k ∈ univ.filter (fun k : Fin N => k.val < 10),F (headPad hN l k) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro k _
      by_cases hk : k.val < 10 <;> simp [headPad,hk,hF]
    _ = _ := by
      symm
      apply sum_bij (fun (i : Fin 10) _ => (⟨i.val,by omega⟩ : Fin N))
      · intro i _
        simp [i.isLt]
      · intro i _ j _ hij
        exact Fin.ext (congrArg (fun z : Fin N => z.val) hij)
      · intro k hk
        have hk' : k.val < 10 := (mem_filter.mp hk).2
        exact ⟨⟨k.val,hk'⟩,mem_univ _,Fin.ext rfl⟩
      · intro i _
        simp [headPad,i.isLt]

private theorem tailPad_sum {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ)
    (F : ℝ → ℝ) (hF : F 0=0) :
    (∑ k,F (tailPad hN l k))=∑ i : Fin 15,F (tails hN l i) := by
  classical
  calc
    _ = ∑ k ∈ univ.filter (fun k : Fin N => N-15 ≤ k.val),F (tailPad hN l k) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro k _
      by_cases hk : N-15 ≤ k.val <;> simp [tailPad,hk,hF]
    _ = _ := by
      symm
      apply sum_bij (fun (i : Fin 15) _ => (⟨N-15+i.val,by omega⟩ : Fin N))
      · intro i _
        simp only [mem_filter,mem_univ,true_and]
        omega
      · intro i _ j _ hij
        apply Fin.ext
        have hi := congrArg Fin.val hij
        dsimp at hi
        omega
      · intro k hk
        have hk' : N-15 ≤ k.val := (mem_filter.mp hk).2
        refine ⟨⟨k.val-(N-15),by omega⟩,mem_univ _,?_⟩
        apply Fin.ext
        dsimp
        omega
      · intro i _
        simp [tailPad,show N-15 ≤ N-15+i.val by omega]

/-- The raw coordinate and square formulas retain the original two boundary
pools and replace only the middle gaps. They also cover N=25 and ties. -/
private theorem concentrated_polynomials {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ)
    (j : Fin N) (hj : j ∈ middle N) (k : Fin N) :
    concentrated (spectralGap l) j k =
      u hN l+v hN l*step N (j.val+1) k+headPad hN l k-tailPad hN l k ∧
    (concentrated (spectralGap l) j k)^2 =
      (u hN l)^2+(2*u hN l*v hN l+(v hN l)^2)*step N (j.val+1) k+
      2*(u hN l+v hN l)*headPad hN l k-2*u hN l*tailPad hN l k+
      (headPad hN l k)^2+(tailPad hN l k)^2 := by
  have hj' : 9 ≤ j.val ∧ j.val < N-15 := (mem_filter.mp hj).2
  by_cases hh : k.val < 10
  · have ht : ¬ N-15 ≤ k.val := by omega
    rw [concentrated_boundary l j hj k (Or.inl hh)]
    simp only [headPad,tailPad,dif_pos hh,dif_neg ht,step,
      if_pos (show k.val < j.val+1 by omega)]
    dsimp [heads,v]
    constructor <;> ring
  · by_cases ht : N-15 ≤ k.val
    · rw [concentrated_boundary l j hj k (Or.inr ht)]
      simp only [headPad,tailPad,dif_neg hh,dif_pos ht,step,
        if_neg (show ¬ k.val < j.val+1 by omega)]
      have hi : (⟨N-15+(k.val-(N-15)),by omega⟩ : Fin N)=k := by
        apply Fin.ext
        dsimp
        omega
      simp only [tails,hi]
      constructor <;> ring
    · rw [concentrated_interior hN l j k (by omega)]
      simp only [headPad,tailPad,dif_neg hh,dif_neg ht]
      constructor
      · ring
      · unfold step
        split_ifs <;> ring

theorem concentrated_raw_moments {N : ℕ} (hN : 25 ≤ N) (l : Fin N → ℝ)
    (j : Fin N) (hj : j ∈ middle N) :
    (∑ k,concentrated (spectralGap l) j k)=
      (N:ℝ)*u hN l+(j.val+1:ℕ)*v hN l+H hN l-D hN l ∧
    (∑ k,(concentrated (spectralGap l) j k)^2)=
      (N:ℝ)*(u hN l)^2+(j.val+1:ℕ)*(2*u hN l*v hN l+(v hN l)^2)+
      2*(u hN l+v hN l)*H hN l-2*u hN l*D hN l+
      headEnergy hN l+tailEnergy hN l := by
  have hJ : j.val+1 ≤ N := by omega
  have hh := headPad_sum hN l (fun x => x) rfl
  have hd := tailPad_sum hN l (fun x => x) rfl
  have ha := headPad_sum hN l (fun x => x^2) (by norm_num)
  have hq := tailPad_sum hN l (fun x => x^2) (by norm_num)
  change (∑ k,headPad hN l k)=H hN l at hh
  change (∑ k,tailPad hN l k)=D hN l at hd
  change (∑ k,(headPad hN l k)^2)=headEnergy hN l at ha
  change (∑ k,(tailPad hN l k)^2)=tailEnergy hN l at hq
  have hpoint (k : Fin N) := (concentrated_polynomials hN l j hj k).1
  have hsquare (k : Fin N) := (concentrated_polynomials hN l j hj k).2
  constructor
  · simp_rw [hpoint]
    simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,hh,hd,sum_step N (j.val+1) hJ]
    ring
  · simp_rw [hsquare]
    simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,hh,hd,ha,hq,sum_step N (j.val+1) hJ]
    ring

/-- Exact arbitrary-real moment identities with the unchanged telescope.
The linear mass scales by U and the square sum by U^2. -/
theorem concentratedMoments : ConcentratedMomentsGap := by
  intro N hN l j hj hu
  dsimp only
  have hm := concentrated_raw_moments hN l j hj
  constructor
  · rw [hm.1]
    unfold mass
    push_cast
    field_simp [ne_of_gt hu] <;> ring
  · rw [hm.2]
    unfold energy mass W
    push_cast
    field_simp [ne_of_gt hu] <;> ring

/-- The physical APPT spectrum satisfies the upper estimate for every n ≥ 19,
by exact concentration and the scalar estimates in the nineteen and larger branches. -/
theorem physical_upper_from_exact_bridges (n : ℕ) (hn : 19 ≤ n)
    (e : (Fin 5 × Fin n) ≃ Fin (5*n)) (l : Fin (5*n) → ℝ)
    (hl : Antitone l) (h0 : ∀ i,0 ≤ l i)
    (h : APPT (diagonal (fun p => (l (e p) : ℂ)))) :
    (∑ i,(l i)^2) ≤ (5/(24*(n:ℝ)))*(∑ i,l i)^2 := by
  let hN : 25 ≤ 5*n := by omega
  by_cases hz : u hN l=0
  · have hlz := homogeneous_zero_actual n (by omega) e l hl h0 h hz
    rw [hlz]
    simp
  have hu : 0 < u hN l := lt_of_le_of_ne (h0 _) (Ne.symm hz)
  have hh := physicalScalarExtraction n hn e l hl h0 h hu
  let r := v hN l/u hN l
  let HH := H hN l/u hN l
  let DD := D hN l/u hN l
  let aa := headEnergy hN l/(u hN l)^2
  let qq := tailEnergy hN l/(u hN l)^2
  let ss := (5*u hN l-10*v hN l-H hN l-D hN l)/u hN l
  have hscalar : Hyp r HH DD aa qq ss := hh
  have hc := concentration_transfer hN (5/(24*(n:ℝ))) (by positivity) l hl h0
  apply hc
  · intro j hj
    exact sum_nonneg (fun i _ => concentrated_nonnegative l hl h0 j i)
  · intro j hj
    have hmid : 9 ≤ j.val ∧ j.val < 5*n-15 := (mem_filter.mp hj).2
    have hident := concentratedMoments (5*n) hN l j hj hu
    dsimp only at hident
    push_cast at hident
    rw [hident.1,hident.2]
    have htheta : (25/(24*(5*(n:ℝ))))=5/(24*(n:ℝ)) := by
      push_cast
      field_simp
      ring
    have hb : energy (5*n) (j.val+1) r HH DD aa qq ≤
        (5/(24*(n:ℝ)))*(mass (5*n) (j.val+1) r HH DD)^2 := by
      by_cases heq : n=19
      · subst n
        have hb' := concentrated_nineteen r HH DD aa qq ss (j.val+1) hscalar
          (by exact_mod_cast (show 10 ≤ j.val+1 by omega))
          (by exact_mod_cast (show j.val+1 ≤ 80 by omega))
        norm_num only [Nat.cast_ofNat] at *
        convert hb' using 1 <;> norm_num
      · have hn20 : 20 ≤ n := by omega
        have hN100 : (100:ℝ) ≤ 5*(n:ℝ) := by exact_mod_cast (show 100 ≤ 5*n by omega)
        have hb' := concentrated_ge100 (5*n) (j.val+1) r HH DD aa qq ss hN100 hscalar
        have hc' := common_loss_nonnegative (5*n) r hN100 hscalar.r0 hscalar.r1
        rw [htheta] at hb'
        linarith only [hb',hc']
    have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (u hN l))
    convert hm using 1 <;> simp only [r,HH,DD,aa,qq,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] <;> ring
end
end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Physical
