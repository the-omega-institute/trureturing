import Batteries.Tactic.OpenPrivate
import CFMPActualAnglePositive257Transient
import CFMPOriginalStrictInverse310Transient
import D5.S3.Geometry.Hyperideal.PositiveFlatClassification
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Tactic

-- UNCOMPILED temporary application package. No source is admitted or published.
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open scoped Matrix
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
open D5.S3.Geometry.Hyperideal.FourCycleCurvature (frame)
open D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface (gram)
open D5.S3.Geometry.Hyperideal.LengthGramBody (lengthGram)
open CFMPGenuineLengthNeighborhood435Transient (genuine sourceCosine)
open CFMPSourceAngleKernel111
open CFMPOriginalSixPairedAngles435Transient (vertexPerm)
open CFMPOriginalAllSideCosines435Transient (relabel gram_relabel)
open CFMPNormalizedInverseTangent107
open CFMPStrictAngleGram296Transient
open CFMPStrictAngleCofactors297Transient
open CFMPCofactorLengthGram303Transient
open CFMPCofactorNormalizedInverse307Transient
open CFMPNormalizedInverseInvolution298Transient
open private delta square_gap cofactor_triangle raw_quotient denominator_pos denominator_sq num_frame delta_frame
  from D5.S3.Geometry.Hyperideal.PositiveFlatClassification
open private normalized_diagonal normalized_gram_symmetric
  from CFMPActualAnglePositive257Transient
open private rawCos_bounds_iff_det_neg from CFMPOriginalAngleInverseCore309Transient
open private remaining_cofactors from CFMPStrictAngleCofactors297Transient

namespace CFMPOriginalForward390

theorem scalar_branch (u v w : ℝ)
    (hu : -1 < u ∧ u < 1) (hv : -1 < v ∧ v < 1)
    (hw : -1 < w ∧ w < 1)
    (hma : 0 < u + v*w) (hmb : 0 < v + u*w)
    (hmc : 0 < w + u*v)
    (hD : 0 < u^2 + v^2 + w^2 + 2*u*v*w - 1) :
    Real.arccos u + Real.arccos v + Real.arccos w < Real.pi := by
  let a := Real.arccos u
  let b := Real.arccos v
  let c := Real.arccos w
  have ha : 0 < a := Real.arccos_pos.mpr hu.2
  have hb : 0 < b := Real.arccos_pos.mpr hv.2
  have hc : 0 < c := Real.arccos_pos.mpr hw.2
  have hap : a < Real.pi := Real.arccos_lt_pi.mpr hu.1
  have hbp : b < Real.pi := Real.arccos_lt_pi.mpr hv.1
  have hcp : c < Real.pi := Real.arccos_lt_pi.mpr hw.1
  have hca : Real.cos a = u := Real.cos_arccos hu.1.le hu.2.le
  have hcb : Real.cos b = v := Real.cos_arccos hv.1.le hv.2.le
  have hcc : Real.cos c = w := Real.cos_arccos hw.1.le hw.2.le
  have huv : 0 < u+v := by
    by_contra h
    have hm := mul_nonpos_of_nonpos_of_nonneg
      (le_of_not_gt h) (show 0 ≤ 1+w by linarith)
    nlinarith only [hm, hma, hmb]
  have hab : a+b < Real.pi := by
    by_contra h
    have hm := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi-b by linarith) hap.le
      (show Real.pi-b ≤ a by linarith)
    rw [Real.cos_pi_sub, hca, hcb] at hm
    linarith
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha hap
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbp
  have hsp : 0 < Real.sin a*Real.sin b := mul_pos hsa hsb
  have hsa2 : Real.sin a^2 = 1-u^2 := by
    nlinarith [Real.sin_sq_add_cos_sq a]
  have hsb2 : Real.sin b^2 = 1-v^2 := by
    nlinarith [Real.sin_sq_add_cos_sq b]
  have hid : (w+u*v)^2-(Real.sin a*Real.sin b)^2 =
      u^2+v^2+w^2+2*u*v*w-1 := by
    rw [mul_pow,hsa2,hsb2]
    ring
  have hmargin : Real.sin a*Real.sin b < w+u*v := by
    nlinarith only [hid,hD,hmc,hsp]
  have hsum : a+b+c < Real.pi := by
    by_contra h
    have hm := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi-(a+b) by linarith) hcp.le
      (show Real.pi-(a+b) ≤ c by linarith)
    rw [Real.cos_pi_sub,Real.cos_add,hca,hcb,hcc] at hm
    nlinarith only [hm,hmargin]
  exact hsum

theorem delta_neg (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hc : ∀ q, -1 < rawCos x q ∧ rawCos x q < 1) : delta x < 0 := by
  let S := Real.sqrt (leftRad x 0)*Real.sqrt (rightRad x 0)
  have hs : 0 < S := denominator_pos x hx 0
  have hb := hc 0
  rw [raw_quotient] at hb
  have hlo : -S < rawNum x 0 := by
    have h := (lt_div_iff₀ hs).mp hb.1
    simpa only [neg_one_mul] using h
  have hhi : rawNum x 0 < S := by
    simpa only [one_mul] using (div_lt_iff₀ hs).mp hb.2
  have hn : (rawNum x 0)^2 < S^2 := by
    nlinarith [mul_pos (sub_pos.mpr hhi) (show 0 < S+rawNum x 0 by linarith)]
  have hs2 : S^2 = leftRad x 0*rightRad x 0 := denominator_sq x hx 0
  have hg := square_gap x 0
  have hp : 0 < (x 0)^2-1 := by nlinarith [hx 0]
  by_contra h
  have hm := mul_nonneg hp.le (le_of_not_gt h)
  nlinarith only [hn,hs2,hg,hm]

-- Each occurrence of cofactor_triangle below is the original private proof.
-- The other equalities only adapt its literal coordinates and normalize polynomials.
theorem representative_polynomials (x : Fin 6 → ℝ) :
    let A := rad (x 0) (x 1) (x 5)
    let B := rad (x 0) (x 2) (x 4)
    let C := rad (x 1) (x 2) (x 3)
    rawNum x 0*rawNum x 1+A*rawNum x 2 = -(x 0*x 1+x 5)*delta x ∧
    rawNum x 0*rawNum x 2+B*rawNum x 1 = -(x 0*x 2+x 4)*delta x ∧
    rawNum x 1*rawNum x 2+C*rawNum x 0 = -(x 1*x 2+x 3)*delta x ∧
    (rawNum x 0)^2*C+(rawNum x 1)^2*B+(rawNum x 2)^2*A+
      2*rawNum x 0*rawNum x 1*rawNum x 2-A*B*C=(delta x)^2 := by
  dsimp only
  have h0 := cofactor_triangle x
  have h0' : rawNum x 0*rawNum x 1+
      rad (x 0) (x 1) (x 5)*rawNum x 2 = -(x 0*x 1+x 5)*delta x := by
    simpa only [leftRad,frame,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue,mul_comm] using h0
  let y : Fin 6 → ℝ := ![x 0,x 2,x 1,x 3,x 5,x 4]
  let z : Fin 6 → ℝ := ![x 1,x 2,x 0,x 4,x 5,x 3]
  have hy : delta y=delta x := by dsimp [y,delta]; ring
  have hzfun : x ∘ frame 1 = z := by
    funext i
    fin_cases i <;> rfl
  have hz : delta z=delta x := by
    rw [← hzfun]
    exact delta_frame x 1
  have hyn (q : Fin 3) : rawNum y q.castSucc.castSucc.castSucc =
      ![rawNum x 0,rawNum x 2,rawNum x 1] q := by
    fin_cases q <;> norm_num [rawNum,frame,numerator,y] <;> ring
  have hzn (q : Fin 3) : rawNum z q.castSucc.castSucc.castSucc =
      ![rawNum x 1,rawNum x 2,rawNum x 0] q := by
    have hh := num_frame x 1 q.castSucc.castSucc.castSucc
    rw [hzfun] at hh
    fin_cases q <;> simpa [frame, Fin.castSucc] using hh
  have h1 := cofactor_triangle y
  have h2 := cofactor_triangle z
  have hy0 := hyn 0; have hy1 := hyn 1; have hy2 := hyn 2
  have hz0 := hzn 0; have hz1 := hzn 1; have hz2 := hzn 2
  change rawNum y 0=rawNum x 0 at hy0
  change rawNum y 1=rawNum x 2 at hy1
  change rawNum y 2=rawNum x 1 at hy2
  change rawNum z 0=rawNum x 1 at hz0
  change rawNum z 1=rawNum x 2 at hz1
  change rawNum z 2=rawNum x 0 at hz2
  rw [hy0,hy1,hy2,hy] at h1
  rw [hz0,hz1,hz2,hz] at h2
  have h1' : rawNum x 0*rawNum x 2+rad (x 0) (x 2) (x 4)*rawNum x 1=
      -(x 0*x 2+x 4)*delta x := by
    simpa only [leftRad,frame,y,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue,mul_comm] using h1
  have h2' : rawNum x 1*rawNum x 2+rad (x 1) (x 2) (x 3)*rawNum x 0=
      -(x 1*x 2+x 3)*delta x := by
    simpa only [leftRad,frame,z,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue,mul_comm] using h2
  refine ⟨h0',h1',h2',?_⟩
  norm_num only [rawNum,frame,numerator,rad,delta,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue]
  ring

theorem representative_data (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hc : ∀ q, -1 < rawCos x q ∧ rawCos x q < 1) :
    let u:=rawCos x 0; let v:=rawCos x 1; let w:=rawCos x 2
    0 < u+v*w ∧ 0 < v+u*w ∧ 0 < w+u*v ∧
      0 < u^2+v^2+w^2+2*u*v*w-1 := by
  let A:=rad (x 0) (x 1) (x 5)
  let B:=rad (x 0) (x 2) (x 4)
  let C:=rad (x 1) (x 2) (x 3)
  have ha : 0 < A := rad_positive _ _ _ (hx 0) (hx 1) (hx 5)
  have hb : 0 < B := rad_positive _ _ _ (hx 0) (hx 2) (hx 4)
  have hc' : 0 < C := rad_positive _ _ _ (hx 1) (hx 2) (hx 3)
  have hsa := (Real.sqrt_pos.mpr ha).ne'
  have hsb := (Real.sqrt_pos.mpr hb).ne'
  have hsc := (Real.sqrt_pos.mpr hc').ne'
  have hd := delta_neg x hx hc
  have xp (q : Fin 6) : 0 < x q := lt_trans (by norm_num) (hx q)
  have hp01 : 0 < -(x 0*x 1+x 5)*delta x := by
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos (add_pos (mul_pos (xp 0) (xp 1)) (xp 5))) hd
  have hp02 : 0 < -(x 0*x 2+x 4)*delta x := by
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos (add_pos (mul_pos (xp 0) (xp 2)) (xp 4))) hd
  have hp12 : 0 < -(x 1*x 2+x 3)*delta x := by
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos (add_pos (mul_pos (xp 1) (xp 2)) (xp 3))) hd
  obtain ⟨h01,h02,h12,hD⟩ := representative_polynomials x
  change (rawNum x 0)^2*C+(rawNum x 1)^2*B+(rawNum x 2)^2*A+
    2*rawNum x 0*rawNum x 1*rawNum x 2-A*B*C=(delta x)^2 at hD
  have hA0 : leftRad x 0=A := rfl
  have hB0 : rightRad x 0=B := rfl
  have hC1 : leftRad x 1=C := rfl
  have hA1 : rightRad x 1=A := by dsimp [rightRad,frame,A,rad]; ring
  have hC2 : leftRad x 2=C := by norm_num [leftRad,frame,C,rad] <;> ring
  have hB2 : rightRad x 2=B := by norm_num [rightRad,frame,B,rad] <;> ring
  have hu : rawCos x 0=rawNum x 0/(Real.sqrt A*Real.sqrt B) := by
    rw [raw_quotient,hA0,hB0]
  have hv : rawCos x 1=rawNum x 1/(Real.sqrt A*Real.sqrt C) := by
    rw [raw_quotient,hC1,hA1,mul_comm (Real.sqrt C)]
  have hw : rawCos x 2=rawNum x 2/(Real.sqrt B*Real.sqrt C) := by
    rw [raw_quotient,hC2,hB2,mul_comm (Real.sqrt C)]
  have e01 : rawCos x 0*rawCos x 1+rawCos x 2=
      (rawNum x 0*rawNum x 1+A*rawNum x 2)/(A*Real.sqrt B*Real.sqrt C) := by
    rw [hu,hv,hw]
    field_simp [ha.ne',hsa,hsb,hsc]
    ring_nf
    simp only [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc'.le]
    <;> ring
  have e02 : rawCos x 0*rawCos x 2+rawCos x 1=
      (rawNum x 0*rawNum x 2+B*rawNum x 1)/(B*Real.sqrt A*Real.sqrt C) := by
    rw [hu,hv,hw]
    field_simp [hb.ne',hsa,hsb,hsc]
    ring_nf
    simp only [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc'.le]
    <;> ring
  have e12 : rawCos x 1*rawCos x 2+rawCos x 0=
      (rawNum x 1*rawNum x 2+C*rawNum x 0)/(C*Real.sqrt A*Real.sqrt B) := by
    rw [hu,hv,hw]
    field_simp [hc'.ne',hsa,hsb,hsc]
    ring_nf
    simp only [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc'.le]
    <;> ring
  have eD : (rawCos x 0)^2+(rawCos x 1)^2+(rawCos x 2)^2+
      2*rawCos x 0*rawCos x 1*rawCos x 2-1=(delta x)^2/(A*B*C) := by
    rw [hu,hv,hw]
    apply (eq_div_iff (by positivity : A*B*C≠0)).mpr
    field_simp [hsa,hsb,hsc]
    ring_nf at hD ⊢
    simp only [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc'.le]
    linear_combination (A*B*C) * hD
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · rw [add_comm, e12]
    exact div_pos (by change 0 < rawNum x 1*rawNum x 2+rad (x 1) (x 2) (x 3)*rawNum x 0; rw [h12]; exact hp12)
      (mul_pos (mul_pos hc' (Real.sqrt_pos.mpr ha)) (Real.sqrt_pos.mpr hb))
  · rw [add_comm, e02]
    exact div_pos (by change 0 < rawNum x 0*rawNum x 2+rad (x 0) (x 2) (x 4)*rawNum x 1; rw [h02]; exact hp02)
      (mul_pos (mul_pos hb (Real.sqrt_pos.mpr ha)) (Real.sqrt_pos.mpr hc'))
  · rw [add_comm, e01]
    exact div_pos (by change 0 < rawNum x 0*rawNum x 1+rad (x 0) (x 1) (x 5)*rawNum x 2; rw [h01]; exact hp01)
      (mul_pos (mul_pos ha (Real.sqrt_pos.mpr hb)) (Real.sqrt_pos.mpr hc'))
  · rw [eD]
    exact div_pos (sq_pos_of_ne_zero hd.ne) (mul_pos (mul_pos ha hb) hc')

-- Original vertex permutations; all three incident edges are tracked explicitly.
def vertexSigma (v : Fin 4) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (![![0,1,2,3],![1,0,2,3],![2,0,1,3],![3,0,1,2]] v)
    (by fin_cases v <;> decide)
def vertexSlots : Fin 4 → Fin 3 → Fin 6 :=
  ![![0,1,2],![0,5,4],![1,5,3],![2,4,3]]

-- Only a finite application of the original formulas; no geometric premise is added.
theorem relabel_vertex_cosine (x : Fin 6 → ℝ) (v : Fin 4) (q : Fin 3) :
    rawCos (relabel x (vertexSigma v)) q.castSucc.castSucc.castSucc =
      rawCos x (vertexSlots v q) := by
  fin_cases v <;> fin_cases q <;>
    norm_num [rawCos,cosine,frame,relabel,vertexSigma,vertexSlots,
      D5.S3.Geometry.Hyperideal.S4OppositePairAction.edgeIndex,rad,numerator,div_div]
    <;> simp only [add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc]
    <;> ring_nf

theorem vertex_sums (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hc : ∀ q, -1 < rawCos x q ∧ rawCos x q < 1) :
    ∀ v : Fin 4, Real.arccos (rawCos x (vertexSlots v 0))+
      Real.arccos (rawCos x (vertexSlots v 1))+
      Real.arccos (rawCos x (vertexSlots v 2)) < Real.pi := by
  intro v
  let y := relabel x (vertexSigma v)
  have hy : ∀ q, 1 < y q := by
    intro q
    fin_cases q <;> exact hx _
  have hyc : ∀ q, -1 < rawCos y q ∧ rawCos y q < 1 := by
    let l : Fin 6 → ℝ := fun i => Real.arcosh (x i)
    have he : (fun i => Real.cosh (l i))=x := funext (fun i => Real.cosh_arcosh (hx i).le)
    have hgen : genuine l := ⟨fun i => Real.arcosh_pos (hx i),by simpa only [sourceCosine,he] using hc⟩
    have hdet := ((CFMPGenuineDomain108Transient.genuine_iff_lengthGram_det_neg l).mp hgen).2
    have hei (i : Fin 6) : Real.cosh (l i)=x i := Real.cosh_arcosh (hx i).le
    have hraw : (gram (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)).det<0 := by
      simpa only [lengthGram,hei,gram] using hdet
    have hyraw : (gram (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)).det<0 := by
      rw [←gram_relabel x (vertexSigma v),Matrix.det_submatrix_equiv_self]
      exact hraw
    intro q
    exact (rawCos_bounds_iff_det_neg y hy q).mpr hyraw
  obtain ⟨hm0,hm1,hm2,hD⟩ := representative_data y hy hyc
  have hs := scalar_branch (rawCos y 0) (rawCos y 1) (rawCos y 2)
    (hyc 0) (hyc 1) (hyc 2) hm0 hm1 hm2 hD
  have h0 := relabel_vertex_cosine x v 0
  have h1 := relabel_vertex_cosine x v 1
  have h2 := relabel_vertex_cosine x v 2
  change rawCos (relabel x (vertexSigma v)) 0=rawCos x (vertexSlots v 0) at h0
  change rawCos (relabel x (vertexSigma v)) 1=rawCos x (vertexSlots v 1) at h1
  change rawCos (relabel x (vertexSigma v)) 2=rawCos x (vertexSlots v 2) at h2
  simpa only [y,h0,h1,h2] using hs

def angle (x : Fin 6 → ℝ) (q : Fin 6) := Real.arccos (rawCos x q)
def angleD (u v w : ℝ) := u^2+v^2+w^2+2*u*v*w-1

theorem forward (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hc : ∀ q, -1 < rawCos x q ∧ rawCos x q < 1) :
    let α := angle x
    let D1 := angleD (Real.cos (α 0)) (Real.cos (α 1)) (Real.cos (α 2))
    let D2 := angleD (Real.cos (α 0)) (Real.cos (α 4)) (Real.cos (α 5))
    (α 0+α 1+α 2<Real.pi) ∧ (α 0+α 5+α 4<Real.pi) ∧
    (α 1+α 5+α 3<Real.pi) ∧ (α 2+α 4+α 3<Real.pi) ∧
    0<D1 ∧ 0<D2 ∧
    x 0=((Real.sin (α 0))^2*Real.cos (α 3)+
      Real.cos (α 1)*Real.cos (α 5)+Real.cos (α 2)*Real.cos (α 4)+
      Real.cos (α 0)*(Real.cos (α 1)*Real.cos (α 4)+Real.cos (α 2)*Real.cos (α 5)))/
      Real.sqrt (D1*D2) := by
  let α := angle x
  let D1 := angleD (Real.cos (α 0)) (Real.cos (α 1)) (Real.cos (α 2))
  let D2 := angleD (Real.cos (α 0)) (Real.cos (α 4)) (Real.cos (α 5))
  have hα (q : Fin 6) : 0 < α q := Real.arccos_pos.mpr (hc q).2
  have hcos (q : Fin 6) : Real.cos (α q)=rawCos x q :=
    Real.cos_arccos (hc q).1.le (hc q).2.le
  have hv := vertex_sums x hx hc
  have hv0 : α 0+α 1+α 2<Real.pi := by simpa only [α,angle,vertexSlots,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hv 0
  have hv1 : α 0+α 5+α 4<Real.pi := by simpa only [α,angle,vertexSlots,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hv 1
  have hv2 : α 1+α 5+α 3<Real.pi := by simpa only [α,angle,vertexSlots,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hv 2
  have hv3 : α 2+α 4+α 3<Real.pi := by simpa only [α,angle,vertexSlots,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hv 3
  let l : Fin 6 → ℝ := fun i => Real.arcosh (x i)
  have hei (i : Fin 6) : Real.cosh (l i)=x i := Real.cosh_arcosh (hx i).le
  have he : (fun i => Real.cosh (l i))=x := funext hei
  have hgen : genuine l := ⟨fun i => Real.arcosh_pos (hx i),by simpa only [sourceCosine,he] using hc⟩
  let G := lengthGram l
  let H := gram (Real.cos (α 3)) (Real.cos (α 4)) (Real.cos (α 5))
    (Real.cos (α 0)) (Real.cos (α 1)) (Real.cos (α 2))
  let K := normalizedInverse G
  have hKsym : K.IsSymm := normalized_gram_symmetric l
  have hdK (i : Fin 4) : K i i=1 := normalized_diagonal l hgen i
  have hk (q : Fin 6) : K (vertexPerm q 2) (vertexPerm q 3) = -Real.cos (α q) := by
    have ht := normalized_source_cosine l hgen q
    simpa only [sourceCosine,he,hcos] using ht
  have h01 : K 0 1= -Real.cos (α 3) := by simpa only [vertexPerm,Equiv.coe_ofBijective,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hk 3
  have h02 : K 0 2= -Real.cos (α 4) := by
    rw [←hKsym.apply 0 2]
    simpa only [vertexPerm,Equiv.coe_ofBijective,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hk 4
  have h03 : K 0 3= -Real.cos (α 5) := by
    rw [←hKsym.apply 0 3]
    simpa only [vertexPerm,Equiv.coe_ofBijective,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hk 5
  have h12 : K 1 2= -Real.cos (α 2) := by
    rw [←hKsym.apply 1 2]
    simpa only [vertexPerm,Equiv.coe_ofBijective,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hk 2
  have h13 : K 1 3= -Real.cos (α 1) := by
    rw [←hKsym.apply 1 3]
    simpa only [vertexPerm,Equiv.coe_ofBijective,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hk 1
  have h23 : K 2 3= -Real.cos (α 0) := by simpa only [vertexPerm,Equiv.coe_ofBijective,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hk 0
  have hN : K=H := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact hdK 0
    · exact h01
    · exact h02
    · exact h03
    · exact (hKsym.apply 0 1).trans h01
    · exact hdK 1
    · exact h12
    · exact h13
    · exact (hKsym.apply 0 2).trans h02
    · exact (hKsym.apply 1 2).trans h12
    · exact hdK 2
    · exact h23
    · exact (hKsym.apply 0 3).trans h03
    · exact (hKsym.apply 1 3).trans h13
    · exact (hKsym.apply 2 3).trans h23
    · exact hdK 3
  have hdet : H.det<0 := strict_angle_gram_det_neg
    (α 3) (α 4) (α 5) (α 2) (α 1) (α 0)
    (hα 3) (hα 4) (hα 5) (hα 2) (hα 1) (hα 0)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨hd,hg⟩ := strict_angle_cofactor_gaps
    (α 3) (α 4) (α 5) (α 2) (α 1) (α 0)
    (hα 3) (hα 4) (hα 5) (hα 2) (hα 1) (hα 0)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hsym : H.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hunit : IsUnit G.det := isUnit_iff_ne_zero.mpr
    (((CFMPGenuineDomain108Transient.genuine_iff_lengthGram_det_neg l).mp hgen).2.ne)
  have hdiag (i : Fin 4) : G i i=1 := by fin_cases i <;> rfl
  have hinvol : normalizedInverse H=G := by
    rw [←hN]
    exact normalizedInverse_involutive G hunit hdiag (inverse_diagonal_positive l hgen)
  have hrecover : lengthGram (cofactorLength H)=G := by
    rw [cofactor_lengthGram_eq H hsym hd hg,
      cofactorGram_eq_normalizedInverse H hdet hd,hinvol]
  have hed := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) hrecover
  have hlen : Real.cosh (cofactorLength H 0)=x 0 := by
    have hh : -Real.cosh (cofactorLength H 0)= -Real.cosh (l 0) := hed
    linarith only [hh,hei 0]
  have hratio := (cofactor_lengths_positive H hd hg 0).2
  have hxratio : x 0=H.adjugate 0 1/Real.sqrt (H.adjugate 0 0*H.adjugate 1 1) := by
    rw [←hlen]
    simpa only [D5.S3.Geometry.Hyperideal.ActualCornerTransport.endpoints,
      Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] using hratio
  obtain ⟨h00,h01c,_,_,_⟩ := gram_cofactor_identities
    (Real.cos (α 3)) (Real.cos (α 4)) (Real.cos (α 5))
    (Real.cos (α 2)) (Real.cos (α 1)) (Real.cos (α 0))
  have h11c := (remaining_cofactors
    (Real.cos (α 3)) (Real.cos (α 4)) (Real.cos (α 5))
    (Real.cos (α 2)) (Real.cos (α 1)) (Real.cos (α 0))).1
  have c00 : H.adjugate 0 0= -D1 := by
    dsimp [D1,angleD]
    rw [show H.adjugate 0 0=_ from h00]
    ring
  have c11 : H.adjugate 1 1= -D2 := by
    dsimp [D2,angleD]
    rw [show H.adjugate 1 1=_ from h11c]
    ring
  have c01 : H.adjugate 0 1=(Real.sin (α 0))^2*Real.cos (α 3)+
      Real.cos (α 1)*Real.cos (α 5)+Real.cos (α 2)*Real.cos (α 4)+
      Real.cos (α 0)*(Real.cos (α 1)*Real.cos (α 4)+Real.cos (α 2)*Real.cos (α 5)) := by
    rw [show H.adjugate 0 1=_ from h01c]
    have hs : (Real.sin (α 0))^2=1-(Real.cos (α 0))^2 := by
      nlinarith only [Real.sin_sq_add_cos_sq (α 0)]
    rw [hs]
    ring
  have hD1 : 0<D1 := by have hh:=hd 0;rw [c00] at hh;linarith
  have hD2 : 0<D2 := by have hh:=hd 1;rw [c11] at hh;linarith
  refine ⟨hv0,hv1,hv2,hv3,hD1,hD2,?_⟩
  rw [c00,c11,c01,neg_mul_neg] at hxratio
  exact hxratio

-- The final checking target has only the original x hypotheses.
example (x : Fin 6 → ℝ) (hx : ∀ q, 1 < x q)
    (hc : ∀ q, -1 < rawCos x q ∧ rawCos x q < 1) :
    let α:=angle x
    let D1:=angleD (Real.cos (α 0)) (Real.cos (α 1)) (Real.cos (α 2))
    let D2:=angleD (Real.cos (α 0)) (Real.cos (α 4)) (Real.cos (α 5))
    (α 0+α 1+α 2<Real.pi) ∧ (α 0+α 5+α 4<Real.pi) ∧
    (α 1+α 5+α 3<Real.pi) ∧ (α 2+α 4+α 3<Real.pi) ∧
    0<D1 ∧ 0<D2 ∧
    x 0=((Real.sin (α 0))^2*Real.cos (α 3)+Real.cos (α 1)*Real.cos (α 5)+
      Real.cos (α 2)*Real.cos (α 4)+Real.cos (α 0)*(Real.cos (α 1)*Real.cos (α 4)+
      Real.cos (α 2)*Real.cos (α 5)))/Real.sqrt (D1*D2) := forward x hx hc

end CFMPOriginalForward390

run_cmd do
  let name := ``CFMPOriginalForward390.forward
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP427 original same-x forward root absent"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP427 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP427 CHECKED {name} axioms={axioms}"
