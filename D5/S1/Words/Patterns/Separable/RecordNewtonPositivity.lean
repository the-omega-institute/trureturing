/- GID: D5/S1/Words/Patterns/Separable/RecordNewtonPositivity
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/RecordNewtonPositivity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Catalan]
   utility: none
   digest: Every Newton kernel composed with the actual separable counting series
     is coefficientwise nonnegative. -/

import D5.S1.Words.Patterns.Separable.RecordPeak
import Mathlib.RingTheory.PowerSeries.Catalan
import Mathlib.RingTheory.PowerSeries.Inverse

namespace D5.S1.Words.Patterns.Separable.RecordNewtonPositivity

open D5.S1.Words.Patterns.Separable.RecordPeak
open scoped BigOperators

-- Exact rational coefficient certificates require the larger elaboration budget.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- All coefficients of every Newton kernel are nonnegative after substitution
of the actual positive separable counting series. This is an unbounded sign law;
it does not assert the correspondence with each actual record fiber. -/
theorem actual_q_record_newton_nonnegative :
    let a : PowerSeries ℚ := PowerSeries.X*(3+2*PowerSeries.X)
    let b : PowerSeries ℚ := PowerSeries.X*(1+PowerSeries.X)^3
    let L : PowerSeries (PowerSeries ℚ) :=
      PowerSeries.invOfUnit (1-PowerSeries.C a*PowerSeries.X) 1
    let M : PowerSeries (PowerSeries ℚ) :=
      L*PowerSeries.subst (PowerSeries.C b*PowerSeries.X^2*L^2)
        (PowerSeries.catalanSeries.map (Nat.castRingHom (PowerSeries ℚ)))
    let t (r : ℕ) := PowerSeries.coeff r M
    ∀ r n, 0 ≤ PowerSeries.coeff n (PowerSeries.subst q
      ((1+PowerSeries.X)^2*(t r+t (r+1))-
        PowerSeries.X*(1-PowerSeries.X)*(1+PowerSeries.X)*
          (t r+2*t (r+1)+t (r+2)))) := by
  dsimp only
  classical
  let a : PowerSeries ℚ := PowerSeries.X * (3+2*PowerSeries.X)
  let b : PowerSeries ℚ := PowerSeries.X * (1+PowerSeries.X)^3
  let c : PowerSeries ℚ := PowerSeries.X * (4+3*PowerSeries.X)
  have cab : c = 4*b-a^2 := by dsimp [a,b,c]; ring
  let L : PowerSeries (PowerSeries ℚ) :=
    PowerSeries.invOfUnit (1-PowerSeries.C a*PowerSeries.X) 1
  have L_inv : (1-PowerSeries.C a*PowerSeries.X)*L = 1 := by
    exact PowerSeries.mul_invOfUnit _ 1 (by simp)
  have L0 : PowerSeries.constantCoeff L = 1 := by
    simp [L, PowerSeries.constantCoeff_invOfUnit]
  let w : PowerSeries (PowerSeries ℚ) := PowerSeries.C b*PowerSeries.X^2*L^2
  have w0 : PowerSeries.constantCoeff w = 0 := by simp [w]
  have hw : PowerSeries.HasSubst w := PowerSeries.HasSubst.of_constantCoeff_zero' w0
  let C : PowerSeries (PowerSeries ℚ) :=
    PowerSeries.catalanSeries.map (Nat.castRingHom (PowerSeries ℚ))
  have C_eq : C^2*PowerSeries.X+1 = C := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom (PowerSeries ℚ)))
      PowerSeries.catalanSeries_sq_mul_X_add_one
    simpa only [map_add,map_mul,map_pow,map_one,PowerSeries.map_X] using h
  let sw (f : PowerSeries (PowerSeries ℚ)) : PowerSeries (PowerSeries ℚ) :=
    PowerSeries.subst w f
  have swC : (sw C)^2*w+1 = sw C := by
    have h := congrArg sw C_eq
    simpa only [sw,PowerSeries.subst_add hw,PowerSeries.subst_mul hw,
      PowerSeries.subst_pow hw,show (PowerSeries.subst w (1 : PowerSeries (PowerSeries ℚ))) = 1 by
        simpa only [map_one] using (PowerSeries.subst_C (1 : PowerSeries ℚ) (a := w)),
      PowerSeries.subst_X hw] using h
  let M : PowerSeries (PowerSeries ℚ) := L*sw C
  have M_eq : M = 1+PowerSeries.C a*PowerSeries.X*M+
      PowerSeries.C b*PowerSeries.X^2*M^2 := by
    have h : (1-PowerSeries.C a*PowerSeries.X)*M = 1+w*(sw C)^2 := by
      dsimp [M]
      calc
        (1-PowerSeries.C a*PowerSeries.X)*(L*sw C) = sw C := by rw [← mul_assoc,L_inv,one_mul]
        _ = 1+w*(sw C)^2 := by linear_combination -swC
    dsimp [M,w] at h ⊢
    linear_combination h
  have M0 : PowerSeries.coeff 0 M = 1 := by
    have h := congrArg PowerSeries.constantCoeff M_eq
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_add,map_one,map_mul,map_pow,PowerSeries.constantCoeff_X,
      mul_zero,zero_mul,zero_add,add_zero,zero_pow (by omega : 2 ≠ 0)] using h
  have M1 : PowerSeries.coeff 1 M = a := by
    have h := congrArg (PowerSeries.coeff 1) M_eq
    simp only [mul_assoc,map_add,PowerSeries.coeff_one,show ¬(1=0) by omega,if_false,
      PowerSeries.coeff_C_mul,PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_X_pow_mul',show ¬(2 ≤ 1) by omega,if_false,M0,
      mul_zero,mul_one,zero_add,add_zero] at h
    exact h
  let Z : PowerSeries (PowerSeries ℚ) := PowerSeries.X
  let A : PowerSeries (PowerSeries ℚ) := PowerSeries.C a
  let B : PowerSeries (PowerSeries ℚ) := PowerSeries.C b
  let K : PowerSeries (PowerSeries ℚ) := PowerSeries.C c
  have Cnum (n : ℕ) [n.AtLeastTwo] :
      PowerSeries.C (OfNat.ofNat n : PowerSeries ℚ) =
        (OfNat.ofNat n : PowerSeries (PowerSeries ℚ)) := map_ofNat PowerSeries.C n
  have coeffNumOuter (v : ℕ) [v.AtLeastTwo] (d : ℕ) (f : PowerSeries (PowerSeries ℚ)) :
      PowerSeries.coeff d ((OfNat.ofNat v : PowerSeries (PowerSeries ℚ))*f) =
        (OfNat.ofNat v : PowerSeries ℚ)*PowerSeries.coeff d f :=
    PowerSeries.coeff_C_mul d f (OfNat.ofNat v)
  have coeffConstOuter (v : ℕ) [v.AtLeastTwo] (d : ℕ) :
      PowerSeries.coeff d (OfNat.ofNat v : PowerSeries (PowerSeries ℚ)) =
        if d=0 then (OfNat.ofNat v : PowerSeries ℚ) else 0 :=
    PowerSeries.coeff_C d (OfNat.ofNat v : PowerSeries ℚ)
  have KB : K = 4*B-A^2 := by
    dsimp only [K,B,A]; rw [cab]; simp only [map_sub,map_mul,map_pow,Cnum]
  have Q : B*Z^2*M^2+(A*Z-1)*M+1 = 0 := by
    dsimp [A,B,Z]
    linear_combination -M_eq
  have QD : (2*B*Z^2*M+A*Z-1)*PowerSeries.derivative (PowerSeries ℚ) M +
      2*B*Z*M^2+A*M = 0 := by
    have h := congrArg (PowerSeries.derivative (PowerSeries ℚ)) Q
    dsimp [A,B,Z] at h ⊢
    simp only [map_add,map_sub,Derivation.leibniz,PowerSeries.derivative_C,
      PowerSeries.derivative_one,PowerSeries.derivative_X,
      PowerSeries.derivative_pow,smul_eq_mul,map_zero] at h
    norm_num at h
    linear_combination h
  have DE : Z*(1-2*A*Z-K*Z^2)*PowerSeries.derivative (PowerSeries ℚ) M+
      (2-3*A*Z-K*Z^2)*M = 2 := by
    have prod : (2*B*Z^2*M+A*Z-1)*
        (Z*(1-2*A*Z-K*Z^2)*PowerSeries.derivative (PowerSeries ℚ) M+
          (2-3*A*Z-K*Z^2)*M-2) = 0 := by
      rw [KB]
      linear_combination Z*(1-2*A*Z-(4*B-A^2)*Z^2)*QD-2*(A*Z-1)*Q
    have nz : 2*B*Z^2*M+A*Z-1 ≠ 0 := by
      intro h
      have h0 := congrArg PowerSeries.constantCoeff h
      dsimp [Z] at h0
      simp at h0
    exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left nz)
  have recurrence (r : ℕ) :
      (r+4 : ℚ) • PowerSeries.coeff (r+2) M =
        (2*r+5 : ℚ) • (a*PowerSeries.coeff (r+1) M)+
        (r+1 : ℚ) • (c*PowerSeries.coeff r M) := by
    have form : Z*PowerSeries.derivative (PowerSeries ℚ) M-
        2*A*Z^2*PowerSeries.derivative (PowerSeries ℚ) M-
        K*Z^3*PowerSeries.derivative (PowerSeries ℚ) M+
        2*M-3*A*Z*M-K*Z^2*M = 2 := by linear_combination DE
    have h := congrArg (PowerSeries.coeff (r+2)) form
    dsimp [Z,A,K] at h
    simp only [mul_assoc,map_add,map_sub,coeffNumOuter,coeffConstOuter,PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_derivative] at h
    rcases r with _ | r
    · try simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
      norm_num at h ⊢
      simpa only [Algebra.smul_def,map_ofNat,PowerSeries.coeff_zero_eq_constantCoeff_apply,mul_assoc] using
        (show 4*PowerSeries.coeff 2 M = 5*a*PowerSeries.coeff 1 M+
          c*PowerSeries.constantCoeff M by linear_combination h)
    · simp only [show 2 ≤ r+1+2 by omega,show 3 ≤ r+1+2 by omega,
        if_true,show r+1+2-2 = r+1 by omega,show r+1+2-3 = r by omega,
        show r+1+2-1 = r+2 by omega] at h
      simp only [Algebra.smul_def,map_add,map_mul,map_natCast,map_ofNat]
      push_cast at h ⊢
      linear_combination h
  obtain ⟨_, scalarCounts, _, _, _, _, _, _, _, _⟩ :=
    D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality
  have qIdentify : q = PowerSeries.X *
      (PowerSeries.largeSchroderSeries.map (Nat.castRingHom ℚ)) := by
    apply PowerSeries.ext
    intro n
    rcases n with _ | n
    · simp [q, PowerSeries.coeff_zero_eq_constantCoeff]
    · simp only [q, PowerSeries.coeff_mk, Nat.succ_ne_zero, if_false,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_map,
        PowerSeries.coeff_largeSchroderSeries, Nat.coe_castRingHom]
      have hc := scalarCounts (n+1) (by omega)
      simpa only [Nat.add_sub_cancel] using congrArg (fun m : ℕ => (m : ℚ)) hc
  have qQuadratic : q = PowerSeries.X + PowerSeries.X*q+q^2 := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      PowerSeries.largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
    simp only [map_add,map_one,map_mul,PowerSeries.map_X,map_pow] at h
    rw [qIdentify]
    linear_combination (PowerSeries.X : PowerSeries ℚ)*h
  have timeRelation : PowerSeries.X*(1+q) = q*(1-q) := by
    linear_combination -qQuadratic
  have q0 : PowerSeries.constantCoeff q = 0 := by simp [q]
  have hq : PowerSeries.HasSubst q := PowerSeries.HasSubst.of_constantCoeff_zero' q0
  let substQ : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := PowerSeries.substAlgHom hq
  have substApply (f : PowerSeries ℚ) : substQ f = PowerSeries.subst q f :=
    congrFun (PowerSeries.coe_substAlgHom (R := ℚ) hq) f
  have substX : substQ PowerSeries.X = q := by
    rw [substApply]; exact PowerSeries.subst_X hq
  have substC (t : ℚ) : substQ (PowerSeries.C t) = PowerSeries.C t := by
    rw [substApply]; exact PowerSeries.subst_C t
  let signKernel : PowerSeries ℚ := 1-2*PowerSeries.X-PowerSeries.X^2
  have qDerivative : substQ signKernel*PowerSeries.derivative ℚ q = (1+q)^2 := by
    have hd := congrArg (PowerSeries.derivative ℚ) qQuadratic
    simp only [map_add,Derivation.leibniz,PowerSeries.derivative_X,
      PowerSeries.derivative_pow,smul_eq_mul] at hd
    dsimp [signKernel]
    simp only [map_sub,map_mul,map_pow,map_one,map_ofNat,substX]
    linear_combination (1+q)*hd-PowerSeries.derivative ℚ q*qQuadratic
  have positiveMul (f g : PowerSeries ℚ)
      (hf : ∀ n, 0 ≤ PowerSeries.coeff n f) (hg : ∀ n, 0 ≤ PowerSeries.coeff n g) :
      ∀ n, 0 ≤ PowerSeries.coeff n (f*g) := by
    intro n
    rw [PowerSeries.coeff_mul]
    exact Finset.sum_nonneg (fun _ _ => mul_nonneg (hf _) (hg _))
  have qPositive (n : ℕ) : 0 ≤ PowerSeries.coeff n q := by
    simp only [q,PowerSeries.coeff_mk]; split_ifs <;> positivity
  have qPowerPositive (d n : ℕ) : 0 ≤ PowerSeries.coeff n (q^d) := by
    induction d generalizing n with
    | zero => simp only [pow_zero,PowerSeries.coeff_one]; split_ifs <;> norm_num
    | succ d ih => rw [pow_succ]; exact positiveMul _ _ ih qPositive n
  have composedPositive (f : PowerSeries ℚ) (hf : ∀ d, 0 ≤ PowerSeries.coeff d f)
      (n : ℕ) : 0 ≤ PowerSeries.coeff n (substQ f) := by
    rw [substApply,PowerSeries.coeff_subst' hq]
    exact finsum_nonneg (fun d => mul_nonneg (hf d) (qPowerPositive d n))
  have coeffNumber (a : ℕ) [a.AtLeastTwo] (n : ℕ) (f : PowerSeries ℚ) :
      PowerSeries.coeff n ((OfNat.ofNat a : PowerSeries ℚ)*f) =
        (OfNat.ofNat a : ℚ)*PowerSeries.coeff n f :=
    PowerSeries.coeff_C_mul n f (OfNat.ofNat a)
  have coeffConstant (a : ℕ) [a.AtLeastTwo] (n : ℕ) :
      PowerSeries.coeff n (OfNat.ofNat a : PowerSeries ℚ) =
        if n=0 then (OfNat.ofNat a : ℚ) else 0 :=
    PowerSeries.coeff_C n (OfNat.ofNat a : ℚ)
  have constantNumber (a : ℕ) [a.AtLeastTwo] :
      PowerSeries.constantCoeff (OfNat.ofNat a : PowerSeries ℚ) =
        (OfNat.ofNat a : ℚ) := PowerSeries.constantCoeff_C (OfNat.ofNat a : ℚ)
  have dNum (a : ℕ) [a.AtLeastTwo] :
      PowerSeries.derivative ℚ (OfNat.ofNat a : PowerSeries ℚ) = 0 :=
    PowerSeries.derivative_C
  have certificateNonneg (f N : PowerSeries ℚ) (cert : ℕ → ℕ)
      (hcert : signKernel*PowerSeries.mk (fun n => (cert n : ℚ)) = N)
      (hpoly : PowerSeries.derivative ℚ f*(1+PowerSeries.X)^2 = N)
      (hf0 : 0 ≤ PowerSeries.constantCoeff f) :
      ∀ n, 0 ≤ PowerSeries.coeff n (substQ f) := by
    let V : PowerSeries ℚ := PowerSeries.mk (fun n => (cert n : ℚ))
    have fDerivative : PowerSeries.derivative ℚ (substQ f) = substQ V := by
      have hp := congrArg substQ hpoly
      simp only [map_add,map_mul,map_pow,map_one,substX] at hp
      have hc := congrArg substQ hcert
      simp only [map_mul] at hc
      have chain : PowerSeries.derivative ℚ (substQ f) =
          substQ (PowerSeries.derivative ℚ f)*PowerSeries.derivative ℚ q := by
        rw [substApply,substApply]; exact PowerSeries.derivative_subst hq
      have hcalc : substQ signKernel*PowerSeries.derivative ℚ (substQ f) = substQ N := by
        rw [chain]
        linear_combination hp+substQ (PowerSeries.derivative ℚ f)*qDerivative
      have hK : substQ signKernel ≠ 0 := by
        intro he
        have hc0 := congrArg PowerSeries.constantCoeff he
        dsimp [signKernel] at hc0
        simp only [map_sub,map_mul,map_pow,map_one,map_ofNat,substX,q0,
          mul_zero,sub_zero] at hc0
        norm_num at hc0
      exact mul_left_cancel₀ hK (hcalc.trans hc.symm)
    intro n
    rcases n with _ | n
    · have hz : PowerSeries.constantCoeff (substQ (f-PowerSeries.C (PowerSeries.constantCoeff f))) = 0 := by
        rw [substApply]
        exact PowerSeries.constantCoeff_subst_eq_zero q0 _ (by simp)
      simp only [map_sub,substC,map_sub,PowerSeries.constantCoeff_C] at hz
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hf0.trans_eq (sub_eq_zero.mp hz).symm
    · have h := composedPositive V (fun d => by simp [V]) n
      rw [← fDerivative,PowerSeries.coeff_derivative] at h
      exact nonneg_of_mul_nonneg_left h (by positivity : (0 : ℚ) < n+1)
  let pc (p : List ℚ) (n : ℕ) : ℚ := p[n]?.getD 0
  let poly (p : List ℚ) : PowerSeries ℚ := PowerSeries.mk (pc p)
  have poly_coeff (p : List ℚ) (n : ℕ) : PowerSeries.coeff n (poly p) = pc p n :=
    PowerSeries.coeff_mk _ _
  have pc_zero (p : List ℚ) (n : ℕ) (hn : p.length ≤ n) : pc p n = 0 := by
    dsimp only [pc]
    rw [List.getElem?_eq_none hn]
    rfl
  have poly_nil : poly [] = 0 := by
    apply PowerSeries.ext; intro n; simp [poly,pc]
  have poly_cons (u : ℚ) (p : List ℚ) : poly (u::p) = PowerSeries.C u+PowerSeries.X*poly p := by
    apply PowerSeries.ext
    intro n
    rcases n with _ | n
    · simp [poly,pc,PowerSeries.coeff_zero_eq_constantCoeff]
    · simp [poly,pc,PowerSeries.coeff_succ_X_mul]
  let pell (s t n : ℕ) : ℕ × ℕ := (fun p : ℕ × ℕ => (p.2,2*p.2+p.1))^[n] (s,t)
  let stream (seed : List ℕ) (s t n : ℕ) : ℕ :=
    if n<seed.length then seed[n]?.getD 0 else (pell s t (n-seed.length)).2
  have stream_tail (seed : List ℕ) (s t n : ℕ) (hn : seed.length ≤ n) :
      stream seed s t (n+2) = 2*stream seed s t (n+1)+stream seed s t n := by
    simp only [stream,if_neg (show ¬n+2<seed.length by omega),
      if_neg (show ¬n+1<seed.length by omega),if_neg (show ¬n<seed.length by omega),
      show n+2-seed.length = (n-seed.length)+2 by omega,
      show n+1-seed.length = (n-seed.length)+1 by omega]
    simp [pell,Function.iterate_succ_apply']
  let nc (p : List ℚ) (n : ℕ) : ℚ :=
    (n+1)*pc p (n+1)+(2*n)*pc p n+((n-1 : ℕ) : ℚ)*pc p (n-1)
  have numerator_coeff (p : List ℚ) (n : ℕ) :
      PowerSeries.coeff n (PowerSeries.derivative ℚ (poly p)*(1+PowerSeries.X)^2) = nc p n := by
    have form : PowerSeries.derivative ℚ (poly p)*(1+PowerSeries.X)^2 =
        PowerSeries.derivative ℚ (poly p)+
        (PowerSeries.X*PowerSeries.derivative ℚ (poly p)+
          PowerSeries.X*PowerSeries.derivative ℚ (poly p))+
        PowerSeries.X^2*PowerSeries.derivative ℚ (poly p) := by ring
    rw [form]
    rcases n with _ | n
    · simp only [map_add,PowerSeries.coeff_zero_X_mul,PowerSeries.coeff_X_pow_mul',
        show ¬(2 ≤ 0) by omega,if_false,add_zero,poly_coeff,nc]
      rw [PowerSeries.coeff_derivative,poly_coeff]
      norm_num
    rcases n with _ | n
    · simp [poly_coeff,nc,PowerSeries.coeff_derivative,PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_X_pow_mul']
      ring
    · simp only [map_add,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_X_pow_mul',
        show 2 ≤ n+1+1 by omega,if_true,show n+1+1-2=n by omega,
        PowerSeries.coeff_derivative,poly_coeff,nc,
        show n+1+1-1=n+1 by omega]
      push_cast
      ring
  have finiteCertificate (p : List ℚ) (seed : List ℕ) (s t : ℕ)
      (hl : p.length+1 ≤ seed.length)
      (hb : ∀ n : Fin (seed.length+2),
        (stream seed s t n : ℚ)-
          (if n.val=0 then 0 else 2*(stream seed s t (n-1) : ℚ))-
          (if n.val<2 then 0 else (stream seed s t (n-2) : ℚ)) = nc p n)
      (h0 : 0 ≤ pc p 0) : ∀ n, 0 ≤ PowerSeries.coeff n (substQ (poly p)) := by
    let cert := stream seed s t
    let V : PowerSeries ℚ := PowerSeries.mk (fun n => (cert n : ℚ))
    have hcert : signKernel*V = PowerSeries.derivative ℚ (poly p)*(1+PowerSeries.X)^2 := by
      have form : signKernel*V = V-(PowerSeries.X*V+PowerSeries.X*V)-PowerSeries.X^2*V := by
        dsimp only [signKernel]; ring
      rw [form]
      apply PowerSeries.ext
      intro n
      rw [numerator_coeff]
      have eqn : (cert n : ℚ)-(if n=0 then 0 else 2*(cert (n-1) : ℚ))-
          (if n<2 then 0 else (cert (n-2) : ℚ)) = nc p n := by
        by_cases hn : n<seed.length+2
        · exact hb ⟨n,hn⟩
        · have hs := stream_tail seed s t (n-2) (by omega)
          rw [show n-2+2=n by omega,show n-2+1=n-1 by omega] at hs
          have hN : nc p n = 0 := by
            simp only [nc,pc_zero p (n+1) (by omega),pc_zero p n (by omega),
              pc_zero p (n-1) (by omega),mul_zero,add_zero]
          rw [hN,if_neg (show n ≠ 0 by omega),if_neg (show ¬n<2 by omega)]
          dsimp only [cert]
          rw [hs]
          push_cast
          ring
      rcases n with _ | n
      · simpa [V,cert,PowerSeries.coeff_zero_eq_constantCoeff] using eqn
      rcases n with _ | n
      · simpa [V,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_X_pow_mul',two_mul] using eqn
      · simpa [V,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_X_pow_mul',
          show 2 ≤ n+1+1 by omega,show n+1+1-2=n by omega,
          show n+1+1-1=n+1 by omega,show n+1+1 ≠ 0 by omega,two_mul] using eqn
    exact certificateNonneg (poly p) _ cert hcert rfl
      (by simpa [poly,PowerSeries.constantCoeff_mk] using h0)
  let t (r : ℕ) : PowerSeries ℚ := PowerSeries.coeff r M
  have t0 : t 0 = 1 := M0
  have t1 : t 1 = a := M1
  have t2 : t 2 = PowerSeries.X+12*PowerSeries.X^2+15*PowerSeries.X^3+5*PowerSeries.X^4 := by
    have h := recurrence 0
    norm_num only at h
    change (4 : ℚ) • t 2 = (5 : ℚ) • (a*t 1)+
      (1 : ℚ) • (c*t 0) at h
    rw [t1,t0] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (4 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t3 : t 3 = 9*PowerSeries.X^2+60*PowerSeries.X^3+99*PowerSeries.X^4+63*PowerSeries.X^5+14*PowerSeries.X^6 := by
    have h := recurrence 1
    norm_num only at h
    change (5 : ℚ) • t 3 = (7 : ℚ) • (a*t 2)+
      (2 : ℚ) • (c*t 1) at h
    rw [t2,t1] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (5 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t4 : t 4 = 2*PowerSeries.X^2+66*PowerSeries.X^3+345*PowerSeries.X^4+658*PowerSeries.X^5+588*PowerSeries.X^6+252*PowerSeries.X^7+42*PowerSeries.X^8 := by
    have h := recurrence 2
    norm_num only at h
    change (6 : ℚ) • t 4 = (9 : ℚ) • (a*t 3)+
      (3 : ℚ) • (c*t 2) at h
    rw [t3,t2] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (6 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t5 : t 5 = 30*PowerSeries.X^3+470*PowerSeries.X^4+2163*PowerSeries.X^5+4500*PowerSeries.X^6+4980*PowerSeries.X^7+3060*PowerSeries.X^8+990*PowerSeries.X^9+132*PowerSeries.X^10 := by
    have h := recurrence 3
    norm_num only at h
    change (7 : ℚ) • t 5 = (11 : ℚ) • (a*t 4)+
      (4 : ℚ) • (c*t 3) at h
    rw [t4,t3] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (7 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t6 : t 6 = 5*PowerSeries.X^3+315*PowerSeries.X^4+3375*PowerSeries.X^5+14364*PowerSeries.X^6+31671*PowerSeries.X^7+40635*PowerSeries.X^8+31680*PowerSeries.X^9+14850*PowerSeries.X^10+3861*PowerSeries.X^11+429*PowerSeries.X^12 := by
    have h := recurrence 4
    norm_num only at h
    change (8 : ℚ) • t 6 = (13 : ℚ) • (a*t 5)+
      (5 : ℚ) • (c*t 4) at h
    rw [t5,t4] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (8 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t7 : t 7 = 105*PowerSeries.X^4+2905*PowerSeries.X^5+24633*PowerSeries.X^6+99396*PowerSeries.X^7+228515*PowerSeries.X^8+326865*PowerSeries.X^9+302610*PowerSeries.X^10+182182*PowerSeries.X^11+69069*PowerSeries.X^12+15015*PowerSeries.X^13+1430*PowerSeries.X^14 := by
    have h := recurrence 5
    norm_num only at h
    change (9 : ℚ) • t 7 = (15 : ℚ) • (a*t 6)+
      (6 : ℚ) • (c*t 5) at h
    rw [t6,t5] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (9 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t8 : t 8 = 14*PowerSeries.X^4+1428*PowerSeries.X^5+25284*PowerSeries.X^6+182812*PowerSeries.X^7+709515*PowerSeries.X^8+1683660*PowerSeries.X^9+2618000*PowerSeries.X^10+2762760*PowerSeries.X^11+1999998*PowerSeries.X^12+980980*PowerSeries.X^13+312312*PowerSeries.X^14+58344*PowerSeries.X^15+4862*PowerSeries.X^16 := by
    have h := recurrence 6
    norm_num only at h
    change (10 : ℚ) • t 8 = (17 : ℚ) • (a*t 7)+
      (7 : ℚ) • (c*t 6) at h
    rw [t7,t6] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (10 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t9 : t 9 = 378*PowerSeries.X^5+16128*PowerSeries.X^6+213948*PowerSeries.X^7+1377540*PowerSeries.X^8+5189745*PowerSeries.X^9+12624930*PowerSeries.X^10+20975760*PowerSeries.X^11+24550344*PowerSeries.X^12+20506122*PowerSeries.X^13+12186720*PowerSeries.X^14+5044104*PowerSeries.X^15+1384344*PowerSeries.X^16+226746*PowerSeries.X^17+16796*PowerSeries.X^18 := by
    have h := recurrence 7
    norm_num only at h
    change (11 : ℚ) • t 9 = (19 : ℚ) • (a*t 8)+
      (8 : ℚ) • (c*t 7) at h
    rw [t8,t7] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (11 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t10 : t 10 = 42*PowerSeries.X^5+6300*PowerSeries.X^6+165060*PowerSeries.X^7+1785000*PowerSeries.X^8+10520775*PowerSeries.X^9+38714940*PowerSeries.X^10+96087225*PowerSeries.X^11+168488775*PowerSeries.X^12+214520670*PowerSeries.X^13+201026280*PowerSeries.X^14+138895848*PowerSeries.X^15+70012800*PowerSeries.X^16+25068030*PowerSeries.X^17+6046560*PowerSeries.X^18+881790*PowerSeries.X^19+58786*PowerSeries.X^20 := by
    have h := recurrence 8
    norm_num only at h
    change (12 : ℚ) • t 10 = (21 : ℚ) • (a*t 9)+
      (9 : ℚ) • (c*t 8) at h
    rw [t9,t8] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (12 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t11 : t 11 = 1386*PowerSeries.X^6+84084*PowerSeries.X^7+1593900*PowerSeries.X^8+14790600*PowerSeries.X^9+81304575*PowerSeries.X^10+293536620*PowerSeries.X^11+740668005*PowerSeries.X^12+1358232645*PowerSeries.X^13+1854551160*PowerSeries.X^14+1910878200*PowerSeries.X^15+1492183704*PowerSeries.X^16+878983776*PowerSeries.X^17+384683310*PowerSeries.X^18+121370480*PowerSeries.X^19+26114550*PowerSeries.X^20+3432198*PowerSeries.X^21+208012*PowerSeries.X^22 := by
    have h := recurrence 9
    norm_num only at h
    change (13 : ℚ) • t 11 = (23 : ℚ) • (a*t 10)+
      (10 : ℚ) • (c*t 9) at h
    rw [t10,t9] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (13 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t12 : t 12 = 132*PowerSeries.X^6+27324*PowerSeries.X^7+989010*PowerSeries.X^8+14838120*PowerSeries.X^9+122200650*PowerSeries.X^10+634858290*PowerSeries.X^11+2256136155*PowerSeries.X^12+5772236850*PowerSeries.X^13+10992849120*PowerSeries.X^14+15923379120*PowerSeries.X^15+17770621968*PowerSeries.X^16+15365843856*PowerSeries.X^17+10281884580*PowerSeries.X^18+5278123620*PowerSeries.X^19+2041091910*PowerSeries.X^20+575628636*PowerSeries.X^21+111791592*PowerSeries.X^22+13372200*PowerSeries.X^23+742900*PowerSeries.X^24 := by
    have h := recurrence 10
    norm_num only at h
    change (14 : ℚ) • t 12 = (25 : ℚ) • (a*t 11)+
      (11 : ℚ) • (c*t 10) at h
    rw [t11,t10] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (14 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t13 : t 13 = 5148*PowerSeries.X^7+420420*PowerSeries.X^8+10741302*PowerSeries.X^9+134841564*PowerSeries.X^10+1008972822*PowerSeries.X^11+5002605270*PowerSeries.X^12+17543250585*PowerSeries.X^13+45416116824*PowerSeries.X^14+89335759968*PowerSeries.X^15+136126237104*PowerSeries.X^16+162646618992*PowerSeries.X^17+153343784880*PowerSeries.X^18+114179762268*PowerSeries.X^19+66828277516*PowerSeries.X^20+30397997058*PowerSeries.X^21+10529983464*PowerSeries.X^22+2684840600*PowerSeries.X^23+475158840*PowerSeries.X^24+52151580*PowerSeries.X^25+2674440*PowerSeries.X^26 := by
    have h := recurrence 11
    norm_num only at h
    change (15 : ℚ) • t 13 = (27 : ℚ) • (a*t 12)+
      (12 : ℚ) • (c*t 11) at h
    rw [t12,t11] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (15 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  have t14 : t 14 = 429*PowerSeries.X^7+117117*PowerSeries.X^8+5585580*PowerSeries.X^9+110564454*PowerSeries.X^10+1205458254*PowerSeries.X^11+8336243916*PowerSeries.X^12+39739102221*PowerSeries.X^13+137784970800*PowerSeries.X^14+360341005563*PowerSeries.X^15+728942670183*PowerSeries.X^16+1160596302138*PowerSeries.X^17+1471103483850*PowerSeries.X^18+1494271193415*PowerSeries.X^19+1218939672951*PowerSeries.X^20+796779372246*PowerSeries.X^21+414387569596*PowerSeries.X^22+169215941895*PowerSeries.X^23+53085962475*PowerSeries.X^24+12351232530*PowerSeries.X^25+2007835830*PowerSeries.X^26+203591745*PowerSeries.X^27+9694845*PowerSeries.X^28 := by
    have h := recurrence 12
    norm_num only at h
    change (16 : ℚ) • t 14 = (29 : ℚ) • (a*t 13)+
      (13 : ℚ) • (c*t 12) at h
    rw [t13,t12] at h
    simp only [Algebra.smul_def,map_ofNat,map_one] at h
    dsimp only [a,c] at h
    apply mul_left_cancel₀ (show (16 : PowerSeries ℚ) ≠ 0 by
      intro hz
      have hc := congrArg PowerSeries.constantCoeff hz
      norm_num [constantNumber] at hc)
    linear_combination h
  let P0 : PowerSeries ℚ := poly [1, 4, 2, -8, -6, 11, 15, 5]
  have pos0 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P0) := by
    exact finiteCertificate
      [1, 4, 2, -8, -6, 11, 15, 5]

      [4, 20, 32, 16, 47, 286, 889, 2224, 5372, 12968]
      12968 31308 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P1 : PowerSeries ℚ := poly [0, 4, 17, 12, -36, -49, 32, 95, 63, 14]
  have pos1 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P1) := by
    exact finiteCertificate
      [0, 4, 17, 12, -36, -49, 32, 95, 63, 14]

      [4, 50, 212, 436, 587, 1168, 3727, 10648, 26822, 65048, 157044, 379136]
      379136 915316 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P2 : PowerSeries ℚ := poly [0, 1, 22, 86, 75, -170, -339, 23, 546, 574, 252, 42]
  have pos2 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P2) := by
    exact finiteCertificate
      [0, 1, 22, 86, 75, -170, -339, 23, 546, 574, 252, 42]

      [1, 48, 444, 1796, 4044, 6450, 12187, 33480, 93210, 237120, 578118, 1396800, 3372180,
       8141160]
      8141160 19654500 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P3 : PowerSeries ℚ := poly
      [0, 0, 11, 135, 485, 489, -832, -2254, -794, 2882, 4536, 3012, 990, 132]
  have pos3 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P3) := by
    exact finiteCertificate
      [0, 0, 11, 135, 485, 489, -832, -2254, -794, 2882, 4536, 3012, 990, 132]

      [0, 22, 493, 3780, 14783, 35184, 61834, 115952, 291194, 789224, 2019432, 4951592,
       11981224, 28929352, 69841644, 168612640]
      168612640 407066924 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P4 : PowerSeries ℚ := poly
      [0, 0, 2, 98, 878, 2949, 3317, -4123, -14870, -10419, 13437, 32937, 29931, 14685, 3861,
       429]
  have pos4 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P4) := by
    exact finiteCertificate
      [0, 0, 2, 98, 878, 2949, 3317, -4123, -14870, -10419, 13437, 32937, 29931, 14685, 3861,
       429]

      [0, 4, 310, 4728, 31829, 121290, 300097, 564704, 1068953, 2530478, 6667185, 17083004,
       42104749, 102087538, 246585273, 595325008, 1437241724, 3469808456]
      3469808456 8376858636 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P5 : PowerSeries ℚ := poly
      [0, 0, 0, 35, 815, 5938, 18947, 23261, -20039, -98273, -99480, 46898, 224444, 267234,
       175318, 68497, 15015, 1430]
  have pos5 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P5) := by
    exact finiteCertificate
      [0, 0, 0, 35, 815, 5938, 18947, 23261, -20039, -98273, -99480, 46898, 224444, 267234,
       175318, 68497, 15015, 1430]

      [0, 0, 105, 3680, 43780, 267562, 998785, 2544156, 5044843, 9709816, 22106296, 56652692,
       144788256, 358325068, 870848793, 2104772256, 5081925550, 12268912216, 29619774292,
       71508460800]
      71508460800 172636695892 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P6 : PowerSeries ℚ := poly
      [0, 0, 0, 5, 425, 6586, 41369, 126966, 167619, -90354, -652095, -851382, -2871, 1439559,
       2220933, 1841268, 954096, 310310, 58344, 4862]
  have pos6 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P6) := by
    exact finiteCertificate
      [0, 0, 0, 5, 425, 6586, 41369, 126966, 167619, -90354, -652095, -851382, -2871, 1439559,
       2220933, 1841268, 954096, 310310, 58344, 4862]

      [0, 0, 15, 1760, 39880, 397294, 2252588, 8269160, 21548388, 44559566, 87447232,
       194168224, 485063841, 1232783050, 3059149352, 7452678392, 18027931498, 43535407656,
       105106214842, 253749072288, 612604451796, 1478957975880]
      1478957975880 3570520403556 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P7 : PowerSeries ℚ := poly
      [0, 0, 0, 0, 119, 4438, 52563, 295179, 879534, 1235037, -325272, -4341768, -6919971,
       -2376798, 8575164, 17488458, 17757597, 11486774, 4938908, 1377272, 226746, 16796]
  have pos7 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P7) := by
    exact finiteCertificate
      [0, 0, 0, 0, 119, 4438, 52563, 295179, 879534, 1235037, -325272, -4341768, -6919971,
       -2376798, 8575164, 17488458, 17757597, 11486774, 4938908, 1377272, 226746, 16796]

      [0, 0, 0, 476, 24094, 408898, 3561089, 19015232, 68845683, 182720816, 391137760,
       783185068, 1712770770, 4183942504, 10552188866, 26217147824, 64012329646, 155005379328,
       374422332316, 903995815560, 2182449554160, 5268900164232, 12720250235340, 30709400634912]
      30709400634912 74139051505164 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P8 : PowerSeries ℚ := poly
      [0, 0, 0, 0, 14, 1820, 42812, 417564, 2148445, 6258520, 9268638, -235420, -28947268,
       -54680355, -33688811, 45465043, 131564628, 161033288, 125380372, 66966536, 24656528,
       6021366, 881790, 58786]
  have pos8 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P8) := by
    exact finiteCertificate
      [0, 0, 0, 0, 14, 1820, 42812, 417564, 2148445, 6258520, 9268638, -235420, -28947268,
       -54680355, -33688811, 45465043, 131564628, 161033288, 125380372, 66966536, 24656528,
       6021366, 881790, 58786]

      [0, 0, 0, 56, 9324, 293832, 4042780, 31669720, 161006968, 576210956, 1552538700,
       3421428280, 6987226593, 15155181666, 36325434247, 90803392144, 225561828172,
       551764061024, 1337613573692, 3232285914032, 7804570475746, 18842192292836,
       45489121660942, 109820457718256, 265130038449532, 640080534617320]
      640080534617320 1545291107684172 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P9 : PowerSeries ℚ := poly
      [0, 0, 0, 0, 0, 420, 22806, 394170, 3315294, 15903282, 45529707, 70635300, 12840024,
       -192668499, -424787574, -361201797, 186556155, 947225808, 1392417470, 1275103700,
       814098244, 371560466, 119760648, 26024110, 3432198, 208012]
  have pos9 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P9) := by
    exact finiteCertificate
      [0, 0, 0, 0, 0, 420, 22806, 394170, 3315294, 15903282, 45529707, 70635300, 12840024,
       -192668499, -424787574, -361201797, 186556155, 947225808, 1392417470, 1275103700,
       814098244, 371560466, 119760648, 26024110, 3432198, 208012]

      [0, 0, 0, 0, 2100, 145236, 3327534, 38977872, 280216710, 1367489790, 4845908268,
       13222660284, 29871687225, 62163708012, 134382333735, 317130194016, 785297330508,
       1947978945444, 4771712059352, 11581202484088, 27998710697374, 67613146117544,
       163238673725290, 394094407784192, 951428257794008, 2296951016145560, 5545330295285428,
       13387611606716416]
      13387611606716416 32320553508718260 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P10 : PowerSeries ℚ := poly
      [0, 0, 0, 0, 0, 42, 7728, 255354, 3524364, 26365713, 119441622, 337411320, 545345325,
       198254520, -1274963205, -3263334537, -3463486518, 156194406, 6496181916, 11575468232,
       12288540814, 9141949104, 4972499082, 1985020402, 569328844, 111464716, 13372200, 742900]
  have pos10 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P10) := by
    exact finiteCertificate
      [0, 0, 0, 0, 0, 42, 7728, 255354, 3524364, 26365713, 119441622, 337411320, 545345325,
       198254520, -1274963205, -3263334537, -3463486518, 156194406, 6496181916, 11575468232,
       12288540814, 9141949104, 4972499082, 1985020402, 569328844, 111464716, 13372200, 742900]

      [0, 0, 0, 0, 210, 47208, 1975050, 35813544, 369070857, 2471149224, 11649017682,
       40930793748, 112887726258, 260555522814, 551927092851, 1193244403248, 2781289617618,
       6822649738488, 16883040844880, 41391301311832, 100569099928696, 243268628827676,
       587562783944086, 1418608566526400, 3424855686868544, 8268339525068744,
       19961538239036632, 48191416390935808, 116344371040966548, 280880158472868904]
      280880158472868904 678104687986704356 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P11 : PowerSeries ℚ := poly
      [0, 0, 0, 0, 0, 0, 1518, 112794, 2663364, 30915258, 210281313, 908478981, 2540081325,
       4257474579, 2231412522, -8341293264, -24868718886, -31298602224, -8744865246,
       41844884906, 92932673042, 113468629318, 96642021192, 60999233468, 28980588432,
       10291988020, 2660176320, 473970200, 52151580, 2674440]
  have pos11 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P11) := by
    exact finiteCertificate
      [0, 0, 0, 0, 0, 0, 1518, 112794, 2663364, 30915258, 210281313, 908478981, 2540081325,
       4257474579, 2231412522, -8341293264, -24868718886, -31298602224, -8744865246,
       41844884906, 92932673042, 113468629318, 96642021192, 60999233468, 28980588432,
       10291988020, 2660176320, 473970200, 52151580, 2674440]

      [0, 0, 0, 0, 0, 9108, 825990, 24556224, 371579142, 3448309194, 21745329903, 99509295612,
       347066311245, 966057008364, 2271887649156, 4892933781888, 10604760571812,
       24482995373292, 59518912744946, 146812172376024, 360038458447566, 875639549629576,
       2119355630224608, 5119978433406912, 12362363847353432, 29845985426221464,
       72054743125860900, 173955567897162624, 419965894715428788, 1013887358943381960,
       2447740612679751468, 5909368584302884896]
      5909368584302884896 14266477781285521260 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P12 : PowerSeries ℚ := poly [0, 3, 5, -7, -12, 8, 17, 6]
  have pos12 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P12) := by
    exact finiteCertificate
      [0, 3, 5, -7, -12, 8, 17, 6]

      [3, 22, 49, 40, 52, 278, 894, 2252, 5440, 13132]
      13132 31704 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P13 : PowerSeries ℚ := poly [0, 1, 13, 24, -18, -60, 6, 86, 65, 15]
  have pos13 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P13) := by
    exact finiteCertificate
      [0, 1, 13, 24, -18, -60, 6, 86, 65, 15]

      [1, 30, 186, 500, 814, 1492, 4172, 11596, 29141, 70668, 170612, 411892]
      411892 994396 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P14 : PowerSeries ℚ := poly
      [0, 0, 0, 0, 0, 0, 0, 5148, 420420, 10715562, 132729168, 954456360, 4309457958,
       12294832839, 19237159422, -1792500309, -91989325278, -249594489906, -363289217292,
       -253626779796, 148916577628, 673196278326, 1018678256596, 1015492013406, 744717961572,
       415269074064, 177029088056, 57017901876, 13472640080, 2208195960, 224652960, 10697760]
  have pos14 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P14) := by
    exact finiteCertificate
      [0, 0, 0, 0, 0, 0, 0, 5148, 420420, 10715562, 132729168, 954456360, 4309457958,
       12294832839, 19237159422, -1792500309, -91989325278, -249594489906, -363289217292,
       -253626779796, 148916577628, 673196278326, 1018678256596, 1015492013406, 744717961572,
       415269074064, 177029088056, 57017901876, 13472640080, 2208195960, 224652960, 10697760]

      [0, 0, 0, 0, 0, 0, 36036, 3507504, 110253858, 1747550376, 16855397988, 109497173448,
       509608582743, 1769413720152, 4720021809135, 9953173356612, 17412716280426,
       28281358144956, 51835005603300, 118752677360612, 304615236458366, 781646647164708,
       1950223812231190, 4769091056966604, 11557890431479792, 27928111360996572,
       67435239876254100, 162806650070417772, 393050898005967616, 948908958131229724,
       2290868892116918064, 5530646749767915772, 13352162391984380168, 32234971533736676108]
      32234971533736676108 77822105459457732384 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let P15 : PowerSeries ℚ := poly
      [0, 0, 0, 0, 0, 0, 0, 429, 117117, 5583435, 109978011, 1177298694, 7772954904,
       33524663991, 94378563756, 152648013966, 15378908253, -644899078287, -1908625644507,
       -3053409741063, -2642750307225, 262564931031, 4800152929663, 8597480830653,
       9678312181369, 7993931309143, 5071589046225, 2505121433899, 960647593065, 281417614695,
       60996287385, 9233504100, 872536050, 38779380]
  have pos15 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ P15) := by
    exact finiteCertificate
      [0, 0, 0, 0, 0, 0, 0, 429, 117117, 5583435, 109978011, 1177298694, 7772954904,
       33524663991, 94378563756, 152648013966, 15378908253, -644899078287, -1908625644507,
       -3053409741063, -2642750307225, 262564931031, 4800152929663, 8597480830653,
       9678312181369, 7993931309143, 5071589046225, 2505121433899, 960647593065, 281417614695,
       60996287385, 9233504100, 872536050, 38779380]

      [0, 0, 0, 0, 0, 0, 3003, 948948, 54028689, 1310225202, 17874575862, 157335187152,
       967866785379, 4379285373108, 15094578158136, 40715244532992, 88343628166827,
       161366733135810, 273388501825119, 504903898880028, 1124985365767629, 2818650715826674,
       7176749448982819, 17905516588807792, 43849931953137709, 106369217868095066,
       257119576881175389, 620902407635684060, 1499053987807296577, 3619055433493156894,
       8737176961920306720, 21093411787620799684, 50924000880522559928, 122941413579146512220,
       296806828040095303908, 716555069659337120036]
      716555069659337120036 1729916967358769543980 (by decide)
      (by dsimp only [pc,nc,stream,pell]; decide +kernel) (by decide)
  let E1 : PowerSeries ℚ := (1+PowerSeries.X)^2*
    (1-PowerSeries.X-2*PowerSeries.X^2+3*PowerSeries.X^3)
  let E2 : PowerSeries ℚ := (1+PowerSeries.X)^2*
    (1-2*PowerSeries.X-2*PowerSeries.X^2+4*PowerSeries.X^3)
  let G (r : ℕ) : PowerSeries ℚ := (1+PowerSeries.X)^2*(t r+t (r+1))-
    PowerSeries.X*(1-PowerSeries.X)*(1+PowerSeries.X)*(t r+2*t (r+1)+t (r+2))
  have aPositive : ∀ n, 0 ≤ PowerSeries.coeff n (substQ a) := by
    apply composedPositive
    intro n
    have h : a = 3*PowerSeries.X+2*PowerSeries.X^2 := by dsimp only [a]; ring
    rw [h]
    simp only [map_add,coeffNumber,PowerSeries.coeff_X,PowerSeries.coeff_X_pow]
    split_ifs <;> norm_num
  have cPositive : ∀ n, 0 ≤ PowerSeries.coeff n (substQ c) := by
    apply composedPositive
    intro n
    have h : c = 4*PowerSeries.X+3*PowerSeries.X^2 := by dsimp only [c]; ring
    rw [h]
    simp only [map_add,coeffNumber,PowerSeries.coeff_X,PowerSeries.coeff_X_pow]
    split_ifs <;> norm_num
  have propagate (F : PowerSeries ℚ) (start : ℕ)
      (hs0 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ (F*t start)))
      (hs1 : ∀ n, 0 ≤ PowerSeries.coeff n (substQ (F*t (start+1)))) :
      ∀ r, start ≤ r → ∀ n, 0 ≤ PowerSeries.coeff n (substQ (F*t r)) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr n
      by_cases h0 : r=start
      · subst r; exact hs0 n
      by_cases h1 : r=start+1
      · subst r; exact hs1 n
      have hprev : ∀ d, 0 ≤ PowerSeries.coeff d (substQ (F*t (r-1))) :=
        ih (r-1) (by omega) (by omega)
      have hprev2 : ∀ d, 0 ≤ PowerSeries.coeff d (substQ (F*t (r-2))) :=
        ih (r-2) (by omega) (by omega)
      have hrec := recurrence (r-2)
      have scaled : ((r-2 : ℕ)+4 : ℚ) • (F*t r) =
          (2*(r-2 : ℕ)+5 : ℚ) • (a*(F*t (r-1)))+
          ((r-2 : ℕ)+1 : ℚ) • (c*(F*t (r-2))) := by
        change ((r-2 : ℕ)+4 : ℚ) • t (r-2+2) =
          (2*(r-2 : ℕ)+5 : ℚ) • (a*t (r-2+1))+
          ((r-2 : ℕ)+1 : ℚ) • (c*t (r-2)) at hrec
        rw [show r-2+2=r by omega,show r-2+1=r-1 by omega] at hrec
        simp only [Algebra.smul_def] at hrec ⊢
        linear_combination F*hrec
      have h := congrArg (fun f => PowerSeries.coeff n (substQ f)) scaled
      simp only [map_add,map_smul,PowerSeries.coeff_smul,smul_eq_mul] at h
      have ha : 0 ≤ PowerSeries.coeff n (substQ (a*(F*t (r-1)))) := by
        rw [map_mul]; exact positiveMul _ _ aPositive hprev n
      have hc : 0 ≤ PowerSeries.coeff n (substQ (c*(F*t (r-2)))) := by
        rw [map_mul]; exact positiveMul _ _ cPositive hprev2 n
      have hh : 0 ≤ ((r-2 : ℕ)+4 : ℚ)*PowerSeries.coeff n (substQ (F*t r)) := by
        rw [h]; exact add_nonneg (mul_nonneg (by positivity) ha) (mul_nonneg (by positivity) hc)
      exact nonneg_of_mul_nonneg_right hh (by positivity)
  have tPositive : ∀ r n, 0 ≤ PowerSeries.coeff n (substQ (t r)) := by
    have h := propagate 1 0
      (by intro n; simp only [one_mul,t0,map_one,PowerSeries.coeff_one]; split_ifs <;> norm_num)
      (by simpa only [one_mul,Nat.zero_add,t1] using aPositive)
    intro r n
    simpa only [one_mul] using h r (by omega) n
  have seedE11 : E1*t 1 = P12 := by rw [t1]; norm_num only [E1,P12,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]; ring
  have seedE12 : E1*t 2 = P13 := by rw [t2]; norm_num only [E1,P13,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]; ring
  have seedE213 : E2*t 13 = P14 := by rw [t13]; norm_num only [E2,P14,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]; ring
  have seedE214 : E2*t 14 = P15 := by rw [t14]; norm_num only [E2,P15,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]; ring
  have E1Positive := propagate E1 1 (by rw [seedE11]; exact pos12)
    (by rw [seedE12]; exact pos13)
  have E2Positive := propagate E2 13 (by rw [seedE213]; exact pos14)
    (by rw [seedE214]; exact pos15)
  have GReduction (r : ℕ) : (r+4 : ℚ) • G r =
      (r+4 : ℚ) • (E1*t r+E2*t (r+1))+
      (3 : ℚ) • (PowerSeries.X*(1-PowerSeries.X)*(1+PowerSeries.X)*
        (c*t r+a*t (r+1))) := by
    have hrec := recurrence r
    change (r+4 : ℚ) • t (r+2) = (2*r+5 : ℚ) • (a*t (r+1))+
      (r+1 : ℚ) • (c*t r) at hrec
    simp only [Algebra.smul_def,map_add,map_mul,map_natCast,map_ofNat,map_one] at hrec ⊢
    dsimp only [G,E1,E2,a,c] at hrec ⊢
    linear_combination -PowerSeries.X*(1-PowerSeries.X)*(1+PowerSeries.X)*hrec
  have lastPositive (r n : ℕ) : 0 ≤ PowerSeries.coeff n
      (substQ (PowerSeries.X*(1-PowerSeries.X)*(1+PowerSeries.X)*(c*t r+a*t (r+1)))) := by
    have hP : substQ (PowerSeries.X*(1-PowerSeries.X)*(1+PowerSeries.X)) =
        PowerSeries.X*(1+q)^2 := by
      simp only [map_mul,map_sub,map_add,map_one,substX]
      linear_combination -(1+q)*timeRelation
    simp only [map_mul,map_add,hP]
    have ht : ∀ d, 0 ≤ PowerSeries.coeff d
        (substQ c*substQ (t r)+substQ a*substQ (t (r+1))) := by
      intro d
      rw [map_add]
      exact add_nonneg (positiveMul _ _ cPositive (tPositive r) d)
        (positiveMul _ _ aPositive (tPositive (r+1)) d)
    have hq1 : ∀ d, 0 ≤ PowerSeries.coeff d (1+q) := by
      intro d; simp only [map_add,PowerSeries.coeff_one]
      split_ifs <;> linarith [qPositive d]
    have hsq : ∀ d, 0 ≤ PowerSeries.coeff d ((1+q)^2) := by
      rw [pow_two]; exact positiveMul _ _ hq1 hq1
    have hx : ∀ d, 0 ≤ PowerSeries.coeff d (PowerSeries.X : PowerSeries ℚ) := by
      intro d; simp only [PowerSeries.coeff_X]; split_ifs <;> norm_num
    exact positiveMul _ _ (positiveMul _ _ hx hsq) ht n
  have GTail (r : ℕ) (hr : 12 ≤ r) (n : ℕ) :
      0 ≤ PowerSeries.coeff n (substQ (G r)) := by
    have h := congrArg (fun f => PowerSeries.coeff n (substQ f)) (GReduction r)
    simp only [map_add,map_smul,PowerSeries.coeff_smul,smul_eq_mul] at h
    have he1 := E1Positive r (by omega) n
    have he2 := E2Positive (r+1) (by omega) n
    have hl := lastPositive r n
    have hn : 0 ≤ (r+4 : ℚ)*PowerSeries.coeff n (substQ (G r)) := by
      rw [h]
      exact add_nonneg (mul_nonneg (by positivity) (add_nonneg he1 he2))
        (mul_nonneg (by norm_num) hl)
    exact nonneg_of_mul_nonneg_right hn (by positivity)
  have small0 : G 0 = P0 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t0,t1,t2]
    norm_num only [P0,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small1 : G 1 = P1 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t1,t2,t3]
    norm_num only [P1,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small2 : G 2 = P2 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t2,t3,t4]
    norm_num only [P2,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small3 : G 3 = P3 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t3,t4,t5]
    norm_num only [P3,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small4 : G 4 = P4 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t4,t5,t6]
    norm_num only [P4,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small5 : G 5 = P5 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t5,t6,t7]
    norm_num only [P5,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small6 : G 6 = P6 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t6,t7,t8]
    norm_num only [P6,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small7 : G 7 = P7 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t7,t8,t9]
    norm_num only [P7,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small8 : G 8 = P8 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t8,t9,t10]
    norm_num only [P8,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small9 : G 9 = P9 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t9,t10,t11]
    norm_num only [P9,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small10 : G 10 = P10 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t10,t11,t12]
    norm_num only [P10,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have small11 : G 11 = P11 := by
    norm_num only [G,Nat.reduceAdd]
    rw [t11,t12,t13]
    norm_num only [P11,a,poly_cons,poly_nil,map_ofNat,map_one,map_zero,map_neg]
    ring
  have GPositive (r n : ℕ) : 0 ≤ PowerSeries.coeff n (substQ (G r)) := by
    by_cases hr : r ≤ 11
    · interval_cases r
      · rw [small0]; exact pos0 n
      · rw [small1]; exact pos1 n
      · rw [small2]; exact pos2 n
      · rw [small3]; exact pos3 n
      · rw [small4]; exact pos4 n
      · rw [small5]; exact pos5 n
      · rw [small6]; exact pos6 n
      · rw [small7]; exact pos7 n
      · rw [small8]; exact pos8 n
      · rw [small9]; exact pos9 n
      · rw [small10]; exact pos10 n
      · rw [small11]; exact pos11 n
    · exact GTail r (by omega) n
  intro r n
  change 0 ≤ PowerSeries.coeff n (PowerSeries.subst q (G r))
  rw [← substApply]
  exact GPositive r n

#print axioms actual_q_record_newton_nonnegative

end D5.S1.Words.Patterns.Separable.RecordNewtonPositivity
