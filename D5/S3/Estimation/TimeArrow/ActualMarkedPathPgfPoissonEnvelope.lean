/- GID: D5/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/ActualMarkedPathPgfPoissonEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native marked counts in compensated finite paths obey a complex Poisson envelope. -/

import D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope

/-- Half the sum of the two destination tilts, centered at one. -/
def tiltU {k : ℕ} (zp zm : Fin k → ℂ) (j : Fin k) : ℂ := (zp j + zm j)/2-1
/-- Half the difference of the two destination tilts. -/
def tiltV {k : ℕ} (zp zm : Fin k → ℂ) (j : Fin k) : ℂ := (zp j - zm j)/2
/-- The compensated total-mass drift of the marked edge tilt. -/
def driftA {M q k : ℕ} (r : ℝ) (S : Support M q) (m : Fin k → Fin M)
    (zp zm : Fin k → ℂ) : ℂ :=
  (∑ j, (tiltU zp zm j + (b r S (.inl (m j)) : ℂ)*tiltV zp zm j))/(2*M)
/-- The physical endpoint-parity drift of the marked edge tilt. -/
def driftB {M q k : ℕ} (r : ℝ) (S : Support M q) (m : Fin k → Fin M)
    (zp zm : Fin k → ℂ) : ℂ :=
  (∑ j, (tiltV zp zm j + (b r S (.inl (m j)) : ℂ)*tiltU zp zm j))/(2*M)
/-- The finite sum of native complete-history masses times actual departure count powers. -/
def actualPGF {M q k : ℕ} (r : ℝ) (S : Support M q) (m : Fin k → Fin M)
    (zp zm : Fin k → ℂ) (T : ℕ) : ℂ :=
  ∑ o : Obs M T .path, (probability r .path S o : ℂ) *
    ∏ j, (zp j)^count .path o (m j) 1 * (zm j)^count .path o (m j) (-1)

set_option maxHeartbeats 1600000 in
-- The proof combines complete-history sums with the normalized feedback estimate.
/-- A finite uniform-start native path PGF is within the Poisson envelope, including zero tilts. -/
theorem actual_marked_path_pgf_poisson_envelope {M q T k : ℕ} {r η : ℝ} (hq : 1 ≤ q) (hqm : q < M)
    (hr : 0 < r) (hr1 : r < 1) (hc1 : compensation M q r < 1)
    (S : Support M q) (_hk : k = 1 ∨ k = 2) (m : Fin k → Fin M)
    (hm : Function.Injective m) (zp zm : Fin k → ℂ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (hA : ‖driftA r S m zp zm‖ ≤ η) (hB : ‖driftB r S m zp zm‖ ≤ η)
    (hT : (T : ℝ) * η ^ 2 ≤ 1 / 10) :
    ‖actualPGF r S m zp zm T-Complex.exp ((T:ℂ)*driftA r S m zp zm)‖ ≤
      20*(T:ℝ)*η^2*Real.exp ((T:ℝ)*(driftA r S m zp zm).re) := by
  classical
  have hM : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hMc : (M:ℂ)≠0 := by exact_mod_cast hM.ne'
  have hN : (2*(M:ℂ))≠0 := by exact_mod_cast (ne_of_gt (show (0:ℝ)<2*M by positivity))
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have law := finite_support_bayes (s:=T) hq hqm hr hr1 hc hc1 Experiment.path
  have hcol := (law.1 S).2
  let u := tiltU zp zm
  let v := tiltV zp zm
  let A := driftA r S m zp zm
  let B := driftB r S m zp zm
  let N : ℂ := 2*M
  let U (x : Vertex M) : ℂ := ∑ j, if x=Sum.inl (m j) then u j else 0
  let W (x : Vertex M) : ℂ := ∑ j, if x=Sum.inl (m j) then v j else 0
  let g (j : Fin k) (x y : Vertex M) : ℂ :=
    (if x=Sum.inl (m j) ∧ chi y=1 then zp j else 1) *
    (if x=Sum.inl (m j) ∧ chi y= -1 then zm j else 1)
  have hcount (n : ℕ) (o : Obs M n .path) (j : Fin k) :
      (zp j)^count .path o (m j) 1*(zm j)^count .path o (m j) (-1) =
      ∏ t : Fin n, g j (o t.castSucc) (o t.succ) := by
    dsimp [g]
    rw [prod_mul_distrib]
    simp only [prod_ite, prod_const, one_pow, mul_one, count, edges]
    rfl
  have hedge (x y : Vertex M) : ∏ j, g j x y = 1+U x+W x*(chi y:ℂ) := by
    by_cases hx : ∃ j, x=Sum.inl (m j)
    · obtain ⟨j,hj⟩ := hx
      have hother (i : Fin k) (hi : i≠j) : x≠Sum.inl (m i) := by
        intro he; have := Sum.inl.inj (hj.symm.trans he)
        exact hi (hm this.symm)
      have hU : U x=u j := by
        dsimp [U]; rw [sum_eq_single j (fun i _ hi => if_neg (hother i hi)) (by simp),if_pos hj]
      have hW : W x=v j := by
        dsimp [W]; rw [sum_eq_single j (fun i _ hi => if_neg (hother i hi)) (by simp),if_pos hj]
      rw [prod_eq_single j (fun i _ hi => by simp [g,hother i hi]) (by simp),hU,hW]
      rcases y with l|l <;> norm_num [g,hj,chi,u,v,tiltU,tiltV] <;> ring
    · have hnone (j : Fin k) : x≠Sum.inl (m j) := fun hj => hx ⟨j,hj⟩
      simp [g,U,W,hnone]
  let K (x y : Vertex M) : ℂ := (transition r S x y:ℂ)*(1+U x+W x*(chi y:ℂ))
  have hmass (n : ℕ) (o : Obs M n .path) :
      (probability r .path S o:ℂ)*
        (∏ j, (zp j)^count .path o (m j) 1*(zm j)^count .path o (m j) (-1)) =
      N⁻¹*∏ t : Fin n, K (o t.castSucc) (o t.succ) := by
    simp_rw [hcount]
    rw [prod_comm]
    simp_rw [hedge]
    simp only [probability, Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_prod,
      Complex.ofReal_natCast,Complex.ofReal_ofNat,prod_mul_distrib,K,N]
    ring
  have hsumbr : ∑ x : Vertex M, b r S x = 0 := by
    have hh := hcol (Sum.inl ⟨0, by omega⟩)
    simp only [transition,chi,mul_one,← sum_div,sum_add_distrib,sum_const,card_univ,
      Fintype.card_sum,Fintype.card_fin,nsmul_eq_mul,mul_one] at hh
    push_cast at hh
    have hn : (2*(M:ℝ))≠0 := by positivity
    apply (div_eq_iff hn).mp at hh
    linarith
  have hsumb : ∑ x : Vertex M, (b r S x:ℂ) = 0 := by exact_mod_cast hsumbr
  have hsumχ : ∑ x : Vertex M, (chi x:ℂ) = 0 := by
    simp [Fintype.sum_sum_type,chi]
  have hχb (x : Vertex M) : (chi x:ℂ)*(b r S x:ℂ)=(b r S x:ℂ) := by
    cases x <;> simp [chi,b]
  have hχU (x : Vertex M) : (chi x:ℂ)*U x=U x := by
    cases x <;> simp [chi,U]
  have hχW (x : Vertex M) : (chi x:ℂ)*W x=W x := by
    cases x <;> simp [chi,W]
  have hsparse (f : Vertex M→ℂ) (a : Fin k→ℂ) :
      (∑ x, f x*(∑ j, if x=Sum.inl (m j) then a j else 0)) =
      ∑ j, f (.inl (m j))*a j := by
    simp_rw [mul_sum,mul_ite,mul_zero]
    rw [sum_comm]
    simp
  have hsumU : ∑ x, U x=∑ j, u j := by
    simpa [U] using hsparse (fun _ => 1) u
  have hsumW : ∑ x, W x=∑ j, v j := by
    simpa [W] using hsparse (fun _ => 1) v
  let α (x : Vertex M) : ℂ := 1+U x+(b r S x:ℂ)*W x
  let β (x : Vertex M) : ℂ := (b r S x:ℂ)*(1+U x)+W x
  have hα : ∑ x, α x=N*(1+A) := by
    dsimp [α]
    rw [sum_add_distrib,sum_add_distrib,hsumU,hsparse (fun x => (b r S x:ℂ)) v]
    simp only [sum_const,card_univ,Fintype.card_sum,Fintype.card_fin,nsmul_eq_mul,mul_one]
    dsimp [N,A,driftA,u,v]
    rw [sum_add_distrib]
    push_cast
    field_simp [hN,hMc]
    ring
  have hχα : ∑ x, (chi x:ℂ)*α x=N*A := by
    have he (x : Vertex M) : (chi x:ℂ)*α x=(chi x:ℂ)+U x+(b r S x:ℂ)*W x := by
      dsimp [α]; rw [mul_add,mul_add,mul_one,hχU,← mul_assoc,hχb]
    simp_rw [he]
    rw [sum_add_distrib,sum_add_distrib,hsumχ,hsumU,zero_add,
      hsparse (fun x => (b r S x:ℂ)) v]
    dsimp [N,A,driftA,u,v]
    rw [sum_add_distrib]
    field_simp [hN,hMc]
  have hβ : ∑ x, β x=N*B := by
    have he (x : Vertex M) : β x=(b r S x:ℂ)+(b r S x:ℂ)*U x+W x := by dsimp [β]; ring
    simp_rw [he]
    rw [sum_add_distrib,sum_add_distrib,hsumb,zero_add,
      hsparse (fun x => (b r S x:ℂ)) u,hsumW]
    dsimp [N,B,driftB,u,v]
    rw [sum_add_distrib]
    field_simp [hN,hMc]
    ring
  have hχβ : ∑ x, (chi x:ℂ)*β x=N*B := by
    have he (x : Vertex M) : (chi x:ℂ)*β x=β x := by
      dsimp [β]; rw [mul_add,← mul_assoc,hχb,hχW]
    simpa only [he] using hβ
  have hK (x y : Vertex M) : K x y=(α x+β x*(chi y:ℂ))/N := by
    cases y <;> dsimp [K,transition,α,β,N,chi] <;> push_cast <;>
      field_simp [hMc] <;> ring
  let p (n : ℕ) (y : Vertex M) : ℂ := N⁻¹*
    ∑ o : Fin (n+1)→Vertex M, if o (Fin.last n)=y then
      ∏ t : Fin n, K (o t.castSucc) (o t.succ) else 0
  have hp0 (y : Vertex M) : p 0 y=N⁻¹ := by
    dsimp [p]
    simp only [Fin.prod_univ_zero]
    rw [← (Equiv.funUnique (Fin 1) (Vertex M)).symm.sum_comp]
    cases y <;> simp [Equiv.funUnique,Equiv.piUnique]
  have hpnext (n : ℕ) (y : Vertex M) : p (n+1) y=∑ x, p n x*K x y := by
    dsimp [p]
    rw [← (Fin.snocEquiv (fun _ : Fin (n+2) => Vertex M)).sum_comp]
    simp only [Fintype.sum_prod_type,Fin.snocEquiv,Equiv.coe_fn_mk,
      Fin.prod_univ_castSucc,Fin.snoc_last,Fin.snoc_castSucc,Fin.succ_castSucc,
      Fin.succ_last]
    rw [sum_comm]
    simp only [sum_ite_eq',mem_univ,if_true]
    symm
    simp_rw [mul_sum,sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro o _
    simp [mul_ite,ite_mul,mul_assoc]
  let R : ℕ → ℂ × ℂ := fun n => Nat.rec (1,0)
    (fun _ f => ((1+A)*f.1+A*f.2,B*f.1+B*f.2)) n
  have hR0 : R 0=(1,0) := rfl
  have hRnext (n : ℕ) : R (n+1)=((1+A)*(R n).1+A*(R n).2,B*(R n).1+B*(R n).2) := rfl
  have hpend (n : ℕ) (y : Vertex M) :
      p n y=((R n).1+(chi y:ℂ)*(R n).2)/N := by
    induction n generalizing y with
    | zero => simp [hp0,R,div_eq_mul_inv]
    | succ n ih =>
      rw [hpnext]
      simp_rw [ih,hK]
      have hex (x : Vertex M) :
          (((R n).1+(chi x:ℂ)*(R n).2)/N)*((α x+β x*(chi y:ℂ))/N) =
          ((R n).1*α x+(R n).2*((chi x:ℂ)*α x)+
            ((R n).1*β x+(R n).2*((chi x:ℂ)*β x))*(chi y:ℂ))/N^2 := by ring
      simp_rw [hex]
      rw [← sum_div,sum_add_distrib,sum_add_distrib,← sum_mul,sum_add_distrib,
        ← mul_sum,← mul_sum,← mul_sum,← mul_sum,hα,hχα,hβ,hχβ,hRnext]
      field_simp [hN,hMc]
  have htotal (n : ℕ) : actualPGF r S m zp zm n=(R n).1 := by
    have hjoin : actualPGF r S m zp zm n=∑ y, p n y := by
      dsimp [actualPGF,p]
      simp_rw [hmass,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro o _
      rw [← mul_sum]
      simp
    rw [hjoin]
    simp_rw [hpend]
    rw [← sum_div,sum_add_distrib,← sum_mul,hsumχ]
    simp only [zero_mul,add_zero,sum_const,card_univ,Fintype.card_sum,
      Fintype.card_fin,nsmul_eq_mul]
    dsimp [N]
    push_cast
    field_simp [hN,hMc]
    ring
  let h : ℂ := 1+A
  have ha : ‖A‖≤η := hA
  have hb : ‖B‖≤η := hB
  have hh : (3/4:ℝ)≤‖h‖ := by
    have hh := norm_sub_norm_le (1:ℂ) (-A)
    simp only [norm_one,norm_neg,sub_neg_eq_add] at hh
    dsimp [h]; linarith
  have hhb : (1/2:ℝ)≤‖h‖-‖B‖ := by linarith
  have hhpos : 0<‖h‖ := by linarith
  have hhne : h≠0 := norm_pos_iff.mp hhpos
  have hdpos : 0<‖h‖-‖B‖ := by linarith
  let X (n : ℕ) : ℂ := (R n).1/h^n
  let Y (n : ℕ) : ℂ := (R n).2/h^n
  let ρ : ℂ := B/h
  have hx0 : X 0=1 := by simp [X,R]
  have hy0 : Y 0=0 := by simp [Y,R]
  have hxnext (n : ℕ) : X (n+1)=X n+(A/h)*Y n := by
    dsimp [X,Y]
    rw [hRnext,pow_succ]
    change (h*(R n).1+A*(R n).2)/(h^n*h) = (R n).1/h^n+(A/h)*((R n).2/h^n)
    field_simp [hhne]
  have hynext (n : ℕ) : Y (n+1)=ρ*(X n+Y n) := by
    dsimp [X,Y,ρ]
    rw [hRnext,pow_succ]
    field_simp [hhne]
  have hρ : ‖ρ‖=‖B‖/‖h‖ := norm_div _ _
  have hρlt : ‖ρ‖<1 := by rw [hρ,div_lt_one hhpos]; linarith
  have hgeom (n : ℕ) : (∑ j ∈ range n, ‖ρ‖^j)≤1/(1-‖ρ‖) := by
    apply (le_div_iff₀ (sub_pos.mpr hρlt)).mpr
    rw [geom_sum_mul_neg]
    linarith [pow_nonneg (norm_nonneg ρ) n]
  have hyfeedback (n : ℕ) : Y n=∑ j ∈ range n, ρ^(n-j)*X j := by
    induction n with
    | zero => simp [hy0]
    | succ n ih =>
      rw [hynext,ih,sum_range_succ]
      have he : (∑ j ∈ range n, ρ^(n+1-j)*X j)=
          ρ*(∑ j ∈ range n, ρ^(n-j)*X j) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        have hn : n+1-j=(n-j)+1 := by have := mem_range.mp hj; omega
        rw [hn,pow_succ]; ring
      rw [he]
      simp only [Nat.add_sub_cancel_left,pow_one]
      ring
  let L : ℕ→ℝ := fun n=>Nat.rec ‖X 0‖ (fun i s=>max s ‖X (i+1)‖) n
  have hL0 : L 0=1 := by simp [L,hx0]
  have hLnext (n : ℕ) : L (n+1)=max (L n) ‖X (n+1)‖ := rfl
  have hLpoint (n j : ℕ) (hj : j≤n) : ‖X j‖≤L n := by
    induction n with
    | zero =>
      have hj0 : j=0 := by omega
      subst j
      exact le_rfl
    | succ n ih =>
      rw [hLnext]
      by_cases hjn : j≤n
      · exact (ih hjn).trans (le_max_left _ _)
      · have hj1 : j=n+1 := by omega
        subst j
        exact le_max_right _ _
  have hLpos (n : ℕ) : 0≤L n := (norm_nonneg _).trans (hLpoint n 0 (Nat.zero_le _))
  have hybound (n : ℕ) : ‖Y n‖≤(‖B‖/(‖h‖-‖B‖))*L n := by
    cases n with
    | zero => rw [hy0,norm_zero]; positivity
    | succ n =>
      have hge : (∑ j ∈ range (n+1), ‖ρ‖^(n-j))≤1/(1-‖ρ‖) := by
        simpa only [Nat.add_sub_cancel] using
          (sum_range_reflect (fun j=>‖ρ‖^j) (n+1)).trans_le (hgeom (n+1))
      have hd : ‖ρ‖/(1-‖ρ‖)=‖B‖/(‖h‖-‖B‖) := by
        rw [hρ]; field_simp [hhpos.ne',hdpos.ne']
      calc
        ‖Y (n+1)‖ = ‖∑ j ∈ range (n+1), ρ^(n+1-j)*X j‖ := congrArg norm (hyfeedback (n+1))
        _ ≤ ∑ j ∈ range (n+1), ‖ρ‖^(n+1-j)*‖X j‖ := by
          simpa only [norm_mul,norm_pow] using norm_sum_le (range (n+1)) (fun j=>ρ^(n+1-j)*X j)
        _ ≤ ∑ j ∈ range (n+1), ‖ρ‖*‖ρ‖^(n-j)*L (n+1) := by
          apply sum_le_sum
          intro j hj
          have hjn : j≤n := by have := mem_range.mp hj; omega
          have hn : n+1-j=(n-j)+1 := by omega
          rw [hn,pow_succ,mul_comm (‖ρ‖^(n-j)) ‖ρ‖]
          exact mul_le_mul_of_nonneg_left (hLpoint (n+1) j (by omega)) (by positivity)
        _ = (‖ρ‖*(∑ j ∈ range (n+1), ‖ρ‖^(n-j)))*L (n+1) := by
          rw [← sum_mul,← mul_sum]
        _ ≤ (‖ρ‖/(1-‖ρ‖))*L (n+1) := by
          rw [div_eq_mul_one_div]
          gcongr
        _ = (‖B‖/(‖h‖-‖B‖))*L (n+1) := by rw [hd]
  let θ : ℝ := ‖A*B‖/(‖h‖*(‖h‖-‖B‖))
  have hθ : 0≤θ := by dsimp [θ]; positivity
  have hθη : θ≤(8/3)*η^2 := by
    dsimp [θ]
    rw [norm_mul]
    apply (div_le_iff₀ (mul_pos hhpos hdpos)).mpr
    have hnum : ‖A‖*‖B‖≤η^2 := by nlinarith [norm_nonneg A,norm_nonneg B]
    have hden : (3/8:ℝ)≤‖h‖*(‖h‖-‖B‖) := by nlinarith
    nlinarith [sq_nonneg η]
  have hincrement (n : ℕ) : ‖X (n+1)-X n‖≤θ*L n := by
    rw [hxnext,add_sub_cancel_left,norm_mul,norm_div]
    calc
      (‖A‖/‖h‖)*‖Y n‖ ≤ (‖A‖/‖h‖)*((‖B‖/(‖h‖-‖B‖))*L n) := by gcongr; exact hybound n
      _ = θ*L n := by dsimp [θ]; rw [norm_mul]; field_simp [hhpos.ne',hdpos.ne']
  have hLgrowth (n : ℕ) : L (n+1)≤(1+θ)*L n := by
    rw [hLnext]
    apply max_le
    · nlinarith [hLpos n]
    · have hn := norm_add_le (X n) (X (n+1)-X n)
      rw [add_sub_cancel] at hn
      have hpn := hLpoint n n le_rfl
      have hi := hincrement n
      nlinarith
  have hLbound (n : ℕ) : L n≤(1+θ)^n := by
    induction n with
    | zero => simp [hL0]
    | succ n ih =>
      exact (hLgrowth n).trans (by rw [pow_succ]; nlinarith)
  have htel (n : ℕ) : X n-1=∑ j ∈ range n, (X (j+1)-X j) := by
    induction n with
    | zero => simp [hx0]
    | succ n ih => rw [sum_range_succ,← ih]; ring
  have hXbound : ‖X T-1‖≤2*(T:ℝ)*θ := by
    have hpow : (1+θ)^T≤Real.exp ((T:ℝ)*θ) := by
      calc
        (1+θ)^T ≤ (Real.exp θ)^T := by
          gcongr
          linarith [Real.add_one_le_exp θ]
        _ = Real.exp ((T:ℝ)*θ) := (Real.exp_nat_mul θ T).symm
    have htime : (T:ℝ)*θ≤4/15 := by
      have := mul_le_mul_of_nonneg_left hθη (Nat.cast_nonneg T : (0:ℝ)≤T)
      nlinarith
    have hnn : (0:ℝ)≤(T:ℝ)*θ := by positivity
    have he : Real.exp ((T:ℝ)*θ)-1≤2*(T:ℝ)*θ := by
      have he := Real.abs_exp_sub_one_le (x:=(T:ℝ)*θ)
        (by rw [abs_of_nonneg hnn]; linarith)
      rw [abs_of_nonneg hnn] at he
      nlinarith only [le_abs_self (Real.exp ((T:ℝ)*θ)-1),he]
    have htelbound : ‖X T-1‖≤(1+θ)^T-1 := by
      rw [htel]
      calc
        ‖∑ j ∈ range T, (X (j+1)-X j)‖ ≤ ∑ j ∈ range T, ‖X (j+1)-X j‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ range T, θ*(1+θ)^j := by
          apply sum_le_sum; intro j _
          exact (hincrement j).trans (mul_le_mul_of_nonneg_left (hLbound j) hθ)
        _ = (1+θ)^T-1 := by
          rw [← mul_sum]
          have hg := geom_sum_mul_add θ T
          rw [add_comm θ 1] at hg
          nlinarith
    exact htelbound.trans ((sub_le_sub_right hpow 1).trans he)
  let δ : ℂ := Complex.log h-A
  let κ : ℝ := ‖A‖^2/(2*(1-‖A‖))
  have hAless : ‖A‖<1 := by linarith
  have hκ : 0≤κ := by dsimp [κ]; positivity
  have hδ : ‖δ‖≤κ := by
    convert Complex.norm_log_one_add_sub_self_le hAless using 1
    dsimp [κ]; field_simp [(sub_pos.mpr hAless).ne']
  have hκη : κ≤(2/3)*η^2 := by
    dsimp [κ]
    apply (div_le_iff₀ (by positivity : 0<2*(1-‖A‖))).mpr
    have hsq : ‖A‖^2≤η^2 := by nlinarith [norm_nonneg A]
    have hden : (3/2:ℝ)≤2*(1-‖A‖) := by linarith
    nlinarith [sq_nonneg η]
  have hTκ : (T:ℝ)*κ≤1/15 := by
    have := mul_le_mul_of_nonneg_left hκη (Nat.cast_nonneg T : (0:ℝ)≤T)
    nlinarith
  have hδT : ‖(T:ℂ)*δ‖≤(T:ℝ)*κ := by
    rw [norm_mul,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg _)
  have hδexp : ‖Complex.exp ((T:ℂ)*δ)-1‖≤2*(T:ℝ)*κ := by
    exact (Complex.norm_exp_sub_one_le (hδT.trans (by linarith))).trans (by nlinarith)
  have hhexact : h^T=Complex.exp ((T:ℂ)*A)*Complex.exp ((T:ℂ)*δ) := by
    calc
      h^T=Complex.exp ((T:ℂ)*Complex.log h) := by
        rw [Complex.exp_nat_mul,Complex.exp_log hhne]
      _ = Complex.exp ((T:ℂ)*A)*Complex.exp ((T:ℂ)*δ) := by
        rw [← Complex.exp_add]
        congr 1
        dsimp [δ]; ring
  have hexpnorm : ‖Complex.exp ((T:ℂ)*A)‖=Real.exp ((T:ℝ)*A.re) := by
    rw [Complex.norm_exp]
    simp
  have hhpbound : ‖h^T‖≤3*Real.exp ((T:ℝ)*A.re) := by
    have hre : ((T:ℂ)*δ).re≤(T:ℝ)*κ :=
      (Complex.re_le_norm _).trans hδT
    have hexpκ : Real.exp ((T:ℝ)*κ)≤3 :=
      (Real.exp_le_exp.mpr (by linarith)).trans Real.exp_one_lt_three.le
    rw [hhexact,norm_mul,hexpnorm,Complex.norm_exp]
    have hmexp := Real.exp_le_exp.mpr hre
    nlinarith [Real.exp_pos ((T:ℝ)*A.re)]
  have hherror : ‖h^T-Complex.exp ((T:ℂ)*A)‖≤
      2*(T:ℝ)*κ*Real.exp ((T:ℝ)*A.re) := by
    have he : h^T-Complex.exp ((T:ℂ)*A)=
        Complex.exp ((T:ℂ)*A)*(Complex.exp ((T:ℂ)*δ)-1) := by rw [hhexact]; ring
    rw [he,norm_mul,hexpnorm]
    nlinarith [Real.exp_pos ((T:ℝ)*A.re)]
  have hfinal : ‖(R T).1-Complex.exp ((T:ℂ)*A)‖≤
      20*(T:ℝ)*η^2*Real.exp ((T:ℝ)*A.re) := by
    have hf : (R T).1=h^T*X T := by dsimp [X]; field_simp [hhne]
    have he : (R T).1-Complex.exp ((T:ℂ)*A)=
        h^T*(X T-1)+(h^T-Complex.exp ((T:ℂ)*A)) := by rw [hf]; ring
    rw [he]
    calc
      ‖h^T*(X T-1)+(h^T-Complex.exp ((T:ℂ)*A))‖ ≤
          ‖h^T‖*‖X T-1‖+‖h^T-Complex.exp ((T:ℂ)*A)‖ := by
        simpa only [norm_mul] using norm_add_le (h^T*(X T-1)) _
      _ ≤ (3*Real.exp ((T:ℝ)*A.re))*(2*(T:ℝ)*θ)+
          2*(T:ℝ)*κ*Real.exp ((T:ℝ)*A.re) := by gcongr
      _ ≤ 20*(T:ℝ)*η^2*Real.exp ((T:ℝ)*A.re) := by
        have ht0 : (0:ℝ)≤T := Nat.cast_nonneg _
        have htθ := mul_le_mul_of_nonneg_left hθη ht0
        have htκ := mul_le_mul_of_nonneg_left hκη ht0
        have hexp0 := Real.exp_pos ((T:ℝ)*A.re)
        have hsum : 6*(T:ℝ)*θ+2*(T:ℝ)*κ≤20*(T:ℝ)*η^2 := by nlinarith
        nlinarith
  rw [htotal]
  exact hfinal

#print axioms actual_marked_path_pgf_poisson_envelope
end D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
