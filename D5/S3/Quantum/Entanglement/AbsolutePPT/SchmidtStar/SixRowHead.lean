/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHead
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: A single nonnegative unit vector and labelled K6 assignment dominate the head norm. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Star
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadScalar
import Mathlib.Algebra.Order.BigOperators.Expect
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset
open scoped BigOperators
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHead
open UniformSchmidtIncidence
noncomputable section

/-- The fifteen slots consist of one distinguished edge, two four-edge
stars, and the six remaining edges. Every slot is a labelled edge. -/
def edgeAt : Fin 15 → Edge 6 :=
  ![⟨(0,1),by decide⟩,⟨(0,2),by decide⟩,⟨(0,3),by decide⟩,
    ⟨(0,4),by decide⟩,⟨(0,5),by decide⟩,⟨(1,2),by decide⟩,
    ⟨(1,3),by decide⟩,⟨(1,4),by decide⟩,⟨(1,5),by decide⟩,
    ⟨(2,3),by decide⟩,⟨(2,4),by decide⟩,⟨(2,5),by decide⟩,
    ⟨(3,4),by decide⟩,⟨(3,5),by decide⟩,⟨(4,5),by decide⟩]

def edgeEquiv : Fin 15 ≃ Edge 6 := Equiv.ofBijective edgeAt (by decide)

def headValue (a : Fin 15 → ℝ) (p : Fin 5 → ℝ) (π : Edge 6 ≃ Fin 15) : ℝ :=
  ∑ e : Edge 6, a (π e)*(Fin.cases 1 p e.val.1)*(Fin.cases 1 p e.val.2)

private def leaf (q : Fin 4 → ℝ) : Fin 6 → ℝ :=
  ![q 0*q 1,q 0*q 2,q 0*q 3,q 1*q 2,q 1*q 3,q 2*q 3]

private theorem leaf_nonneg (q : Fin 4 → ℝ) (hq : ∀ i,0 ≤ q i) :
    ∀ i,0 ≤ leaf q i := by
  intro i
  have h0 := hq 0
  have h1 := hq 1
  have h2 := hq 2
  have h3 := hq 3
  fin_cases i <;> simp [leaf] <;> positivity

private theorem four_product (q : Fin 4 → ℝ) (beta : ℝ)
    (hb : 0 ≤ beta) (hq : ∀ i,beta ≤ q i) :
    3*beta*Real.sqrt (∑ i,(q i)^2) ≤ ∑ i,leaf q i := by
  let e : Fin 4 → ℝ := fun i => q i-beta
  let B := ∑ i,e i
  let C := ∑ i,leaf e i
  have he : ∀ i,0 ≤ e i := fun i => sub_nonneg.mpr (hq i)
  have hq0 : ∀ i,0 ≤ q i := fun i => hb.trans (hq i)
  apply FiveRowP2Star.star_product_bound beta B C (∑ i,leaf q i)
    (Real.sqrt (∑ i,(q i)^2)) hb
    (sum_nonneg (fun i _ => he i))
    (sum_nonneg (fun i _ => leaf_nonneg e he i))
    (sum_nonneg (fun i _ => leaf_nonneg q hq0 i)) (Real.sqrt_nonneg _) ?_ ?_
  · simp [B,C,e,leaf,Fin.sum_univ_succ]
    ring
  · rw [Real.sq_sqrt (sum_nonneg (fun i _ => sq_nonneg _))]
    simp [B,C,e,leaf,Fin.sum_univ_succ]
    ring

private theorem good_cycle (d c : Fin 6 → ℝ) (b : ℝ)
    (hb : 6*b ≤ (∑ i,d i)*(∑ i,c i)) :
    ∃ k : Fin 6, b ≤ ∑ i,d (i+k)*c i := by
  have hav : (∑ k : Fin 6, ∑ i : Fin 6,d (i+k)*c i) =
      (∑ i,d i)*(∑ i,c i) := by
    rw [sum_comm]
    simp_rw [← sum_mul]
    have hs (i : Fin 6) : (∑ k : Fin 6,d (i+k)) = ∑ k,d k :=
      Equiv.sum_comp (Equiv.addLeft i) d
    simp_rw [hs]
    rw [mul_sum]
  obtain ⟨k, _, hk⟩ := exists_le_of_sum_le
    (s := (univ : Finset (Fin 6))) univ_nonempty
    (f := fun _ => b) (g := fun k => ∑ i,d (i+k)*c i) (by simpa [hav] using hb)
  exact ⟨k,hk⟩

private def rotate (k : Fin 6) : Equiv.Perm (Fin 15) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin 9)) (Equiv.addRight k)).trans finSumFinEquiv)

private theorem slot_value (a : Fin 15 → ℝ) (s t : ℝ) (q : Fin 4 → ℝ)
    (k : Fin 6) (σ : Equiv.Perm (Fin 15)) :
    headValue a (Fin.cases s (fun i => t*q i))
      (edgeEquiv.symm.trans ((rotate k).trans σ)) =
    a (σ 0)*s +
      t*(∑ i : Fin 4,(a (σ ⟨1+i.val,by omega⟩)+s*a (σ ⟨5+i.val,by omega⟩))*q i)+
      t^2*∑ i : Fin 6,a (σ (Fin.natAdd 9 (i+k)))*leaf q i := by
  unfold headValue
  rw [← edgeEquiv.sum_comp]
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply]
  have he (i : Fin 15) : edgeEquiv i = edgeAt i := rfl
  have hv : (Fin.cases 1 (Fin.cases s (fun i => t*q i)) : Fin 6 → ℝ) =
      ![1,s,t*q 0,t*q 1,t*q 2,t*q 3] := by
    funext i
    fin_cases i <;> rfl
  simp only [he,hv]
  fin_cases k <;>
    norm_num [edgeAt,rotate,leaf,Fin.sum_univ_succ,
      finSumFinEquiv,Fin.add_def,Fin.addCases]
  <;> ring

private theorem correction_monotone (t A v u : ℝ)
    (ht : 0 ≤ t) (hu : 0 < u) (huv : u ≤ v) (hA : A ≤ t*u^2) :
    t*u+A/u ≤ t*v+A/v := by
  have hv : 0 < v := hu.trans_le huv
  have hprod : 0 ≤ (v-u)*(t*v*u-A) := by
    apply mul_nonneg (sub_nonneg.mpr huv)
    have hm := mul_nonneg (mul_nonneg ht hu.le) (sub_nonneg.mpr huv)
    nlinarith only [hm,hA]
  have he : t*v+A/v-(t*u+A/u) = (v-u)*(t*v*u-A)/(v*u) := by
    field_simp [ne_of_gt hv,ne_of_gt hu]
    <;> ring
  have hp := div_nonneg hprod (mul_nonneg hv.le hu.le)
  rw [← he] at hp
  linarith only [hp]

private theorem sorted_head (M : ℝ) (b c : Fin 4 → ℝ) (d : Fin 6 → ℝ)
    (hM : 0 ≤ M) (hb : ∀ i,0 ≤ b i) (hc : ∀ i,0 ≤ c i)
    (hd : ∀ i,0 ≤ d i) (hbM : ∀ i,b i ≤ M)
    (hbc : ∀ i j,c j ≤ b i) (hcd : ∀ i j,d j ≤ c i) :
    ∃ (s : ℝ) (q : Fin 4 → ℝ) (k : Fin 6),
      0 ≤ s ∧ (∀ i,0 ≤ q i) ∧ s^2+(∑ i,(q i)^2)=1 ∧
      Real.sqrt (M^2+(∑ i,(b i)^2)+(∑ i,(c i)^2)+∑ i,(d i)^2) ≤
        M*s+(∑ i,(b i+s*c i)*q i)+∑ i,d (i+k)*leaf q i := by
  classical
  let X := ∑ i,(b i)^2
  let Y := ∑ i,(c i)^2
  let Z := ∑ i,(d i)^2
  have hX0 : 0 ≤ X := sum_nonneg (fun i _ => sq_nonneg _)
  have hY0 : 0 ≤ Y := sum_nonneg (fun i _ => sq_nonneg _)
  have hZ0 : 0 ≤ Z := sum_nonneg (fun i _ => sq_nonneg _)
  have hYX : Y ≤ X := by
    apply sum_le_sum
    intro i _
    exact (sq_le_sq₀ (hc i) (hb i)).mpr (hbc i i)
  have hXM : X ≤ 4*M^2 := by
    have ht := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 4))) =>
      (sq_le_sq₀ (hb i) hM).mpr (hbM i))
    simpa [X] using ht
  by_cases hY : Y=0
  · have hcz (i : Fin 4) : c i=0 := by
      have ht : (c i)^2 ≤ Y := single_le_sum (fun j _ => sq_nonneg _) (mem_univ i)
      rw [hY] at ht
      nlinarith only [ht]
    have hdz (i : Fin 6) : d i=0 := by
      have ht := hcd 0 i
      rw [hcz 0] at ht
      exact le_antisymm ht (hd i)
    have hZ : Z=0 := by simp [Z,hdz]
    let L := Real.sqrt (M^2+X)
    have hL2 : L^2=M^2+X := Real.sq_sqrt (by positivity)
    by_cases hL : L=0
    · refine ⟨1,fun _ => 0,0,by norm_num,fun _ => le_rfl,by simp,?_⟩
      change Real.sqrt (M^2+X+Y+Z) ≤ _
      rw [hY,hZ]
      have hMX : M^2+X=0 := by simpa [hL] using hL2.symm
      simpa [hMX,leaf,hdz] using hM
    · have hLp : 0 < L := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hL)
      refine ⟨M/L,fun i => b i/L,0,div_nonneg hM hLp.le,
        fun i => div_nonneg (hb i) hLp.le,?_,?_⟩
      · simp_rw [div_pow]
        rw [← sum_div]
        change M^2/L^2+X/L^2=1
        rw [← add_div,← hL2,div_self (pow_ne_zero 2 hL)]
      · change Real.sqrt (M^2+X+Y+Z) ≤ _
        rw [hY,hZ]
        simp only [add_zero,hcz,hdz,mul_zero,zero_mul,add_zero,sum_const_zero]
        have he : M*(M/L)+(∑ i,b i*(b i/L))=L := by
          calc
            _ = (M^2+X)/L := by simp [X,Fin.sum_univ_succ]; ring
            _ = L := by rw [← hL2]; field_simp [hL]
        exact le_of_eq (by simpa [L] using he.symm)
  · have hYp : 0 < Y := lt_of_le_of_ne hY0 (Ne.symm hY)
    have hXp : 0 < X := hYp.trans_le hYX
    obtain ⟨j,_,hj⟩ := exists_max_image (univ : Finset (Fin 6)) d univ_nonempty
    let delta := d j
    let R := ∑ i,d i
    have hdelta : 0 ≤ delta := hd j
    have hR : 0 ≤ R := sum_nonneg (fun i _ => hd i)
    have hdc : ∀ i,delta ≤ c i := fun i => hcd i j
    have hdd : ∀ i,d i ≤ delta := fun i => hj i (mem_univ i)
    have hZdelta : Z ≤ delta*R := by
      dsimp [Z,R]
      rw [mul_sum]
      apply sum_le_sum
      intro i _
      nlinarith only [mul_nonneg (hd i) (sub_nonneg.mpr (hdd i))]
    have hZsix : Z ≤ 6*delta^2 := by
      have ht := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 6))) =>
        (sq_le_sq₀ (hd i) hdelta).mpr (hdd i))
      simpa [Z] using ht
    have hYfour : 4*delta^2 ≤ Y := by
      have ht := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 4))) =>
        (sq_le_sq₀ hdelta (hc i)).mpr (hdc i))
      simpa [Y] using ht
    have hZY : Z ≤ (3/2)*Y := by linarith only [hZsix,hYfour]
    let r := Real.sqrt X
    have hr : 0 < r := Real.sqrt_pos.mpr hXp
    have hr2 : r^2=X := Real.sq_sqrt hX0
    let alpha := M/r
    let kappa := Y/X
    let eta := Z/Y
    have halpha : 1/2 ≤ alpha := by
      apply (le_div_iff₀ hr).mpr
      nlinarith only [hXM,hr2,hM]
    have hkappa : 0 ≤ kappa := div_nonneg hY0 hX0
    have hkappa1 : kappa ≤ 1 := (div_le_one hXp).mpr hYX
    have heta : 0 ≤ eta := div_nonneg hZ0 hY0
    have heta1 : eta ≤ 3/2 := (div_le_iff₀ hYp).mpr hZY
    have hkh : kappa*eta=Z/X := by
      dsimp [kappa,eta]
      field_simp [ne_of_gt hYp,ne_of_gt hXp]
      <;> ring
    let W := 1+kappa*eta
    let L := Real.sqrt (alpha^2+1+kappa*eta)
    let s := alpha/L
    let t := Real.sqrt W/L
    let Tn := Real.sqrt (1+(2*s+s^2)*kappa)
    let T0 := r*Tn
    have hW : 0 < W := by dsimp [W]; positivity
    have hL : 0 < L := by dsimp [L]; apply Real.sqrt_pos.mpr; positivity
    have hs : 0 ≤ s := div_nonneg (by linarith only [halpha]) hL.le
    have ht : 0 < t := div_pos (Real.sqrt_pos.mpr hW) hL
    have hTn : 0 < Tn := by dsimp [Tn]; apply Real.sqrt_pos.mpr; positivity
    have hT0 : 0 < T0 := mul_pos hr hTn
    have hL2 : L^2=alpha^2+W := by
      dsimp [L,W]
      rw [Real.sq_sqrt (by positivity)]
      ring
    have hW2 := Real.sq_sqrt hW.le
    have hn : s^2+t^2=1 := by
      dsimp [s,t]
      field_simp [ne_of_gt hL]
      nlinarith only [hL2,hW2]
    have ht1 : t ≤ 1 := by nlinarith only [hn,ht,sq_nonneg s]
    have hTn2 : Tn^2=1+(2*s+s^2)*kappa := Real.sq_sqrt (by positivity)
    have hT02 : T0^2=X+(2*s+s^2)*Y := by
      dsimp only [T0]
      rw [mul_pow,hr2,hTn2]
      dsimp [kappa]
      field_simp [ne_of_gt hXp]
      <;> ring
    have hT0lower : (1+s)^2*Y ≤ T0^2 := by
      rw [hT02]
      nlinarith only [hYX]
    let z : Fin 4 → ℝ := fun i => b i+s*c i
    let T := Real.sqrt (∑ i,(z i)^2)
    have hz : ∀ i,0 ≤ z i := fun i => add_nonneg (hb i) (mul_nonneg hs (hc i))
    have hT2 : T^2=∑ i,(z i)^2 := Real.sq_sqrt (sum_nonneg (fun i _ => sq_nonneg _))
    let U := ∑ i,b i*c i
    have hUY : Y ≤ U := by
      apply sum_le_sum
      intro i _
      nlinarith only [mul_nonneg (hc i) (sub_nonneg.mpr (hbc i i))]
    have hTsplit : T^2=X+2*s*U+s^2*Y := by
      rw [hT2]
      simp [X,Y,U,z,Fin.sum_univ_succ]
      ring
    have hTcompare : T0 ≤ T := by
      apply (sq_le_sq₀ hT0.le (Real.sqrt_nonneg _)).mp
      rw [hT02,hTsplit]
      nlinarith only [mul_nonneg hs (sub_nonneg.mpr hUY)]
    have hT : 0 < T := hT0.trans_le hTcompare
    let q : Fin 4 → ℝ := fun i => z i/T
    have hq : ∀ i,0 ≤ q i := fun i => div_nonneg (hz i) hT.le
    have hqn : ∑ i,(q i)^2=1 := by
      simp_rw [q,div_pow]
      rw [← sum_div,← hT2,div_self (pow_ne_zero 2 (ne_of_gt hT))]
    have hzb : ∀ i,(1+s)*delta ≤ z i := by
      intro i
      have hdb := (hdc i).trans (hbc i i)
      have hm := mul_le_mul_of_nonneg_left (hdc i) hs
      dsimp [z]
      nlinarith only [hdb,hm]
    have hP := four_product z ((1+s)*delta) (by positivity) hzb
    let P := ∑ i,leaf z i
    have hP' : 3*(1+s)*delta*T ≤ P := by simpa [P,T,mul_assoc] using hP
    have hleaf : (∑ i,leaf q i)=P/T^2 := by
      simp [P,q,leaf,Fin.sum_univ_succ]
      ring
    have hRP : 3*(1+s)*Z*T ≤ R*P := by
      have ha := mul_le_mul_of_nonneg_left hP' hR
      have hb := mul_le_mul_of_nonneg_left hZdelta
        (show 0 ≤ 3*(1+s)*T by positivity)
      nlinarith only [ha,hb]
    have hav : 6*((1+s)*Z/(2*T)) ≤ R*(∑ i,leaf q i) := by
      rw [hleaf]
      suffices hav' : 6*((1+s)*Z/(2*T)) ≤ R*P/T^2 by
        simpa only [mul_div_assoc] using hav'
      apply (le_div_iff₀ (by positivity : 0 < T^2)).mpr
      have he : (6*((1+s)*Z/(2*T)))*T^2=3*(1+s)*Z*T := by
        field_simp [ne_of_gt hT]
        <;> ring
      rw [he]
      exact hRP
    obtain ⟨ell,hell⟩ := good_cycle d (leaf q) ((1+s)*Z/(2*T)) hav
    have hhalf : (1+s)*Z/2 ≤ T0^2 := by
      have ha := mul_le_mul_of_nonneg_left hZY (show 0 ≤ 1+s by positivity)
      have hb := mul_nonneg hs (show 0 ≤ (1+s)*Y by positivity)
      have hbase : 0 ≤ (1+s)*Y := by positivity
      nlinarith only [ha,hb,hT0lower,hbase]
    have hA : t^2*(1+s)*Z/2 ≤ t*T0^2 := by
      have ha := mul_nonneg (sub_nonneg.mpr ht1) (show 0 ≤ (1+s)*Z/2 by positivity)
      have hb := mul_le_mul_of_nonneg_left hhalf ht.le
      have hmul := mul_nonneg ht.le ha
      nlinarith only [hmul,hb]
    have hmono := correction_monotone t (t^2*(1+s)*Z/2) T T0 ht.le hT0 hTcompare hA
    have hmono' : t*T0+t^2*(1+s)*Z/(2*T0) ≤ t*T+t^2*(1+s)*Z/(2*T) := by
      convert hmono using 1 <;> ring
    have hbound := SixRowHeadScalar.recipe_bound alpha kappa eta halpha hkappa hkappa1 heta heta1
    change Real.sqrt (alpha^2+1+kappa+kappa*eta) ≤
      alpha*s+t*Tn+t^2*(1+s)*kappa*eta/(2*Tn) at hbound
    have har : r*alpha=M := by dsimp [alpha]; field_simp [ne_of_gt hr]
    have hrad : r^2*(alpha^2+1+kappa+kappa*eta)=M^2+X+Y+Z := by
      calc
        _ = (r*alpha)^2+r^2+r^2*kappa+r^2*(kappa*eta) := by ring
        _ = _ := by
          simp only [har,hr2,hkh]
          dsimp [kappa]
          field_simp [ne_of_gt hXp]
          <;> ring
    have hroot : r*Real.sqrt (alpha^2+1+kappa+kappa*eta)=Real.sqrt (M^2+X+Y+Z) := by
      apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
      have haSq := Real.sq_sqrt (show 0 ≤ alpha^2+1+kappa+kappa*eta by positivity)
      have hfSq := Real.sq_sqrt (show 0 ≤ M^2+X+Y+Z by positivity)
      rw [mul_pow,haSq,hfSq]
      exact hrad
    have hcorr : r*(kappa*eta)/Tn=Z/T0 := by
      rw [hkh]
      dsimp only [T0]
      field_simp [ne_of_gt hr,ne_of_gt hTn,ne_of_gt hXp]
      nlinarith only [congrArg (fun x : ℝ => x*Z) hr2]
    have hright : r*(alpha*s+t*Tn+t^2*(1+s)*kappa*eta/(2*Tn)) =
        M*s+t*T0+t^2*(1+s)*Z/(2*T0) := by
      calc
        _ = (r*alpha)*s+t*T0+(t^2*(1+s)/2)*(r*(kappa*eta)/Tn) := by
          dsimp only [T0]
          ring
        _ = _ := by rw [har,hcorr]; ring
    have hscalar := mul_le_mul_of_nonneg_left hbound hr.le
    rw [hroot,hright] at hscalar
    have hhead : Real.sqrt (M^2+X+Y+Z) ≤ M*s+t*T+t^2*∑ i,d (i+ell)*leaf q i := by
      have ha := mul_le_mul_of_nonneg_left hell (sq_nonneg t)
      have ha' : t^2*(1+s)*Z/(2*T) ≤ t^2*∑ i,d (i+ell)*leaf q i := by
        convert ha using 1 <;> ring
      calc
        _ ≤ M*s+t*T0+t^2*(1+s)*Z/(2*T0) := hscalar
        _ ≤ M*s+t*T+t^2*(1+s)*Z/(2*T) := by linarith only [hmono']
        _ ≤ _ := by linarith only [ha']
    refine ⟨s,fun i => t*q i,ell,hs,fun i => mul_nonneg ht.le (hq i),?_,?_⟩
    · simp_rw [mul_pow,← mul_sum,hqn,mul_one]
      exact hn
    · have hdot : (∑ i,z i*q i)=T := by
        calc
          _ = (∑ i,(z i)^2)/T := by
            rw [sum_div]
            apply sum_congr rfl
            intro i _
            dsimp only [q]
            ring
          _ = T := by rw [← hT2]; field_simp [ne_of_gt hT]
      have he : M*s+(∑ i,(b i+s*c i)*(t*q i))+
          (∑ i,d (i+ell)*leaf (fun j => t*q j) i) =
          M*s+t*T+t^2*∑ i,d (i+ell)*leaf q i := by
        rw [← hdot]
        simp [z,leaf,Fin.sum_univ_succ]
        ring
      rw [he]
      exact hhead

/-- One unit vector and one edge-label bijection control all fifteen terms,
including repeated weights and vanishing coordinates. -/
theorem head_exists (a : Fin 15 → ℝ) (ha : ∀ i,0 ≤ a i) :
    ∃ (p : Fin 5 → ℝ) (π : Edge 6 ≃ Fin 15),
      (∀ i,0 ≤ p i) ∧ (∑ i,(p i)^2=1) ∧
      Real.sqrt (∑ i,(a i)^2) ≤ headValue a p π := by
  classical
  let σ := Tuple.sort (fun i => -a i)
  let w : Fin 15 → ℝ := fun i => a (σ i)
  have hw : ∀ i,0 ≤ w i := fun i => ha (σ i)
  have hwo : Antitone w := by
    intro i j hij
    have hh := Tuple.monotone_sort (fun i => -a i) hij
    change -w i ≤ -w j at hh
    linarith only [hh]
  let M := w 0
  let b : Fin 4 → ℝ := fun i => w ⟨1+i.val,by omega⟩
  let c : Fin 4 → ℝ := fun i => w ⟨5+i.val,by omega⟩
  let d : Fin 6 → ℝ := fun i => w (Fin.natAdd 9 i)
  obtain ⟨s,q,k,hs,hq,hn,hhead⟩ := sorted_head M b c d (hw 0)
    (fun i => hw _) (fun i => hw _) (fun i => hw _)
    (fun i => hwo (by change 0 ≤ 1+i.val; omega))
    (fun i j => hwo (by change 1+i.val ≤ 5+j.val; omega))
    (fun i j => hwo (by change 5+i.val ≤ 9+j.val; omega))
  let p : Fin 5 → ℝ := Fin.cases s q
  let π := edgeEquiv.symm.trans ((rotate k).trans σ)
  refine ⟨p,π,?_,?_,?_⟩
  · intro i
    exact Fin.cases hs hq i
  · simpa only [p,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ] using hn
  · have hsum : (∑ i,(w i)^2)=∑ i,(a i)^2 := Equiv.sum_comp σ (fun i => (a i)^2)
    have hsplit : (∑ i,(a i)^2)=M^2+(∑ i,(b i)^2)+(∑ i,(c i)^2)+∑ i,(d i)^2 := by
      rw [← hsum]
      simp [M,b,c,d,Fin.sum_univ_succ]
      ring
    have hv := slot_value a s 1 q k σ
    have hv' : headValue a p π = M*s+(∑ i,(b i+s*c i)*q i)+∑ i,d (i+k)*leaf q i := by
      simpa [p,π,M,b,c,d,w] using hv
    rw [hsplit,hv']
    exact hhead

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHead
