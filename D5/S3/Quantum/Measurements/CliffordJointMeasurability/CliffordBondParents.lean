/- GID: D5/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/CliffordJointMeasurability/CliffordBondParents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Fourier vacuum yields a normalized parent with sharp cycle marginals. -/
/-
proof_shape: cycle_majorana_parent: content
escape_witness: cycle_majorana_parent
admission_basis: escape-witness
Direct frozen dependencies: none on the baseline; supporting lane modules are first-freeze dependencies.
Information-escape registration is paused under CLAUDE.md section 3.9.
proof_shape: odd_mode_trig_sums: bind-only; consumer: odd_phase_sum
proof_shape: odd_phase_sum: bind-only; consumer: modeCoeff_bond
proof_shape: modeCoeff_bond: bind-only; consumer: cycle_majorana_parent
proof_shape: phase_pi: bind-only; consumer: phase_odd_multiple_pi
proof_shape: phase_odd_multiple_pi: bind-only; consumer: modeCoeff_closing
proof_shape: modeCoeff_closing: bind-only; consumer: cycle_majorana_parent
proof_shape: majorana_pair_square: bind-only; consumer: imaginary_bond_square
proof_shape: majorana_pair_relation: bind-only; consumer: imaginary_bond_relation
proof_shape: imaginary_bond_square: bind-only; consumer: uniform_majorana_parent
proof_shape: imaginary_bond_relation: bind-only; consumer: uniform_majorana_parent
proof_shape: bool_snoc_sum: bind-only; consumer: monomialMap_sum
proof_shape: monomialMap_sum: bind-only; consumer: monomial_signed_sum
proof_shape: outcomeSign_not: bind-only; consumer: monomialMap_push
proof_shape: monomialMap_push: bind-only; consumer: monomial_signed_sum
proof_shape: monomial_signed_sum: bind-only; consumer: normalized_monomial_parent
proof_shape: monomialMap_psd: bind-only; consumer: normalized_monomial_parent
proof_shape: normalized_monomial_parent: bind-only; consumer: uniform_majorana_parent
proof_shape: uniform_majorana_parent: bind-only; consumer: cycle_majorana_parent
proof_shape: consecutive_majorana_parent: bind-only; consumer: odd_path_JM_threshold
-/
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
namespace D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordBondParents
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.ShiftedFourierOperatorCertificate
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.FourierCliffordVacuum
noncomputable section
private lemma odd_mode_trig_sums {L : ℕ} (hL : 0 < L) :
    (∑ r : Fin L, Real.cos (cycleFrequency L r))=0 ∧
    (∑ r : Fin L, Real.sin (cycleFrequency L r))=(Real.sin (theta L))⁻¹ := by
  have hθ := theta_pos hL
  have he := theta_mul_L hL
  have hsin : Real.sin (theta L) ≠ 0 := by
    have hLR : (1:ℝ) ≤ L := by exact_mod_cast hL
    have hlt : theta L < Real.pi := by nlinarith [Real.pi_pos]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ hlt)
  have hc := Real.sin_mul_sum_cos L (2*theta L) (theta L)
  have hs := Real.sin_mul_sum_sin L (2*theta L) (theta L)
  have ha : (L:ℝ)*(2*theta L)/2=Real.pi/2 := by nlinarith [he]
  have hb : ((L:ℝ)-1)*(2*theta L)/2+theta L=Real.pi/2 := by nlinarith [he]
  rw [show 2*theta L/2=theta L by ring,ha,hb,Real.sin_pi_div_two,Real.cos_pi_div_two,mul_zero] at hc
  rw [show 2*theta L/2=theta L by ring,ha,hb,Real.sin_pi_div_two,one_mul] at hs
  have hc' := (mul_eq_zero.mp hc).resolve_left hsin
  have hs' : (∑ r ∈ Finset.range L, Real.sin (2*theta L*(r:ℝ)+theta L))=(Real.sin (theta L))⁻¹ := by
    calc
      _ = (Real.sin (theta L))⁻¹*(Real.sin (theta L)*_) := by rw [← mul_assoc,inv_mul_cancel₀ hsin,one_mul]
      _ = _ := by rw [hs,mul_one]
  have hcfin : (∑ r : Fin L, Real.cos (cycleFrequency L r))=
      ∑ r ∈ Finset.range L, Real.cos (2*theta L*(r:ℝ)+theta L) := by
    change (∑ r : Fin L, (fun r : ℕ => Real.cos ((2*(r:ℝ)+1)*theta L)) r)=_
    rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => Real.cos ((2*(r:ℝ)+1)*theta L)) L]
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    ring
  have hsfin : (∑ r : Fin L, Real.sin (cycleFrequency L r))=
      ∑ r ∈ Finset.range L, Real.sin (2*theta L*(r:ℝ)+theta L) := by
    change (∑ r : Fin L, (fun r : ℕ => Real.sin ((2*(r:ℝ)+1)*theta L)) r)=_
    rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => Real.sin ((2*(r:ℝ)+1)*theta L)) L]
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    ring
  exact ⟨hcfin.trans hc',hsfin.trans hs'⟩
private lemma odd_phase_sum {L : ℕ} (hL : 0 < L) :
    (∑ r : Fin L, (fun x : ℝ => (Real.probChar x : ℂ)) (-cycleFrequency L r))= -Complex.I*(Real.sin (theta L):ℂ)⁻¹ := by
  have ht := odd_mode_trig_sums hL
  have he : ∀ r : Fin L, (fun x : ℝ => (Real.probChar x : ℂ)) (-cycleFrequency L r)=
      (Real.cos (cycleFrequency L r):ℂ)-Complex.I*(Real.sin (cycleFrequency L r):ℂ) := by
    intro r
    change Complex.exp (((-cycleFrequency L r : ℝ) : ℂ) * Complex.I) = _
    rw [Complex.exp_mul_I]
    simp only [Complex.ofReal_neg,Complex.cos_neg,Complex.sin_neg,Complex.ofReal_cos,Complex.ofReal_sin]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Complex.ofReal_sum,← Complex.ofReal_sum,ht.1,ht.2]
  simp only [Complex.ofReal_zero,Complex.ofReal_inv,zero_sub,neg_mul]
private lemma modeCoeff_bond {L : ℕ} (hL : 0 < L) (j k : Fin (2*L)) (hjk : k.val=j.val+1) :
    Complex.I*(4*∑ r : Fin L, star (modeCoeff L r j)*modeCoeff L r k)=
      (1/((L:ℝ)*Real.sin (theta L)):ℂ) := by
  have ht : ∀ r : Fin L, star (modeCoeff L r j)*modeCoeff L r k=
      (modeScale L*modeScale L)*(fun x : ℝ => (Real.probChar x : ℂ)) (-cycleFrequency L r) := by
    intro r
    rw [modeCoeff,modeCoeff,star_mul,modeScale_star,phase_star]
    calc
      _ = (modeScale L*modeScale L)*((fun x : ℝ => (Real.probChar x : ℂ)) (-(-(j:ℝ)*cycleFrequency L r))*(fun x : ℝ => (Real.probChar x : ℂ)) (-(k:ℝ)*cycleFrequency L r)) := by ring
      _ = _ := by
        rw [phase_mul]
        congr 2
        have hk : (k:ℝ)=(j:ℝ)+1 := by exact_mod_cast hjk
        rw [hk]
        ring
  simp_rw [ht]
  rw [← Finset.mul_sum,odd_phase_sum hL,modeScale_square hL]
  have hn : (L:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_natCast,
    Nat.cast_mul,Nat.cast_ofNat,mul_inv]
  ring_nf
  simp [Complex.I_sq]
end
noncomputable section
private lemma phase_pi : (fun x : ℝ => (Real.probChar x : ℂ)) Real.pi= -1 := by simp [Real.probChar_apply]
private lemma phase_odd_multiple_pi (r : ℕ) : (fun x : ℝ => (Real.probChar x : ℂ)) ((2*(r:ℝ)+1)*Real.pi)= -1 := by
  have he : (2*(r:ℝ)+1)*Real.pi=(r:ℝ)*(2*Real.pi)+Real.pi := by ring
  rw [he,← phase_mul,phase_pi]
  have hp : (fun x : ℝ => (Real.probChar x : ℂ)) ((r:ℝ)*(2*Real.pi))=1 := by
    simp only [Real.probChar_apply]
    rw [show (((r:ℝ)*(2*Real.pi):ℝ):ℂ)*Complex.I=(r:ℂ)*(2*Real.pi*Complex.I) by push_cast;ring,
      Complex.exp_nat_mul]
    simp
  rw [hp,one_mul]
private lemma modeCoeff_closing {L : ℕ} (hL : 0 < L) (j k : Fin (2*L))
    (hj : j.val+1=2*L) (hk : k.val=0) :
    (-Complex.I)*(4*∑ r : Fin L, star (modeCoeff L r j)*modeCoeff L r k)=
      (1/((L:ℝ)*Real.sin (theta L)):ℂ) := by
  have ht : ∀ r : Fin L, star (modeCoeff L r j)*modeCoeff L r k=
      -(modeScale L*modeScale L)*(fun x : ℝ => (Real.probChar x : ℂ)) (-cycleFrequency L r) := by
    intro r
    rw [modeCoeff,modeCoeff,star_mul,modeScale_star,phase_star]
    have hjR : (j:ℝ)=2*(L:ℝ)-1 := by
      have hh : (j:ℝ)+1=2*(L:ℝ) := by exact_mod_cast hj
      linarith
    have hkR : (k:ℝ)=0 := by exact_mod_cast hk
    have ha : -(-(j:ℝ)*cycleFrequency L r)+(-(k:ℝ)*cycleFrequency L r)=
        (2*(r:ℝ)+1)*Real.pi+ -cycleFrequency L r := by
      have he := theta_mul_L hL
      rw [hjR,hkR]
      unfold cycleFrequency
      push_cast
      nlinarith [he]
    calc
      _ = (modeScale L*modeScale L)*((fun x : ℝ => (Real.probChar x : ℂ)) (-(-(j:ℝ)*cycleFrequency L r))*(fun x : ℝ => (Real.probChar x : ℂ)) (-(k:ℝ)*cycleFrequency L r)) := by ring
      _ = _ := by rw [phase_mul,ha,← phase_mul,phase_odd_multiple_pi];ring
  simp_rw [ht]
  rw [← Finset.mul_sum,odd_phase_sum hL,modeScale_square hL]
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_natCast,
    Nat.cast_mul,Nat.cast_ofNat,mul_inv]
  ring_nf
  simp [Complex.I_sq]
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
variable {ι : Type*} [DecidableEq ι]
private lemma majorana_pair_square (g : ι → R) (hsq : ∀ j, g j*g j=1)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (j k : ι) (hjk : j ≠ k) :
    (g j*g k)*(g j*g k)= -(1:R) := by
  exact anticommuting_product_square (g j) (g k) (hsq j) (hsq k) (hanti j k hjk)
private lemma majorana_pair_relation (g : ι → R) (hsq : ∀ j, g j*g j=1)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (j k l : ι) (hjk : j ≠ k) :
    g l*(g j*g k)=(if l=j ∨ l=k then (-1:ℂ) else 1) • ((g j*g k)*g l) := by
  have hrel (i : ι) : g i * g l = (if i = l then (1 : ℂ) else -1) • (g l * g i) := by
    by_cases hil : i = l
    · subst i; simp
    · simpa [hil] using hanti i l hil
  have h := signed_product (g j) (g k) (g l)
    (if j = l then 1 else -1) (if k = l then 1 else -1) (hrel j) (hrel k)
  have hsign : (if j = l then (1 : ℂ) else -1) * (if k = l then 1 else -1) =
      if l = j ∨ l = k then -1 else 1 := by
    by_cases hlj : l = j
    · subst l; simp [hjk, Ne.symm hjk]
    · by_cases hlk : l = k
      · subst l; simp [hjk]
      · simp [hlj, hlk, Ne.symm hlj, Ne.symm hlk]
  rw [hsign] at h
  by_cases he : l = j ∨ l = k
  · simp only [he, ↓reduceIte, neg_one_smul] at h ⊢
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  · simpa only [he, ↓reduceIte, one_smul] using h.symm
private lemma imaginary_bond_square (g : ι → R) (hsq : ∀ j, g j*g j=1)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (j k : ι) (hjk : j ≠ k)
    (c : ℂ) (hc : c*c= -1) : (c • (g j*g k))*(c • (g j*g k))=1 := by
  rw [smul_mul_assoc,mul_smul_comm,smul_smul,hc,majorana_pair_square g hsq hanti j k hjk]
  simp
private lemma imaginary_bond_relation (g : ι → R) (hsq : ∀ j, g j*g j=1)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) (j k l : ι) (hjk : j ≠ k) (c : ℂ) :
    g l*(c • (g j*g k))=(if l=j ∨ l=k then (-1:ℂ) else 1) • ((c • (g j*g k))*g l) := by
  rw [mul_smul_comm,majorana_pair_relation g hsq hanti j k l hjk,smul_mul_assoc,smul_smul,smul_smul]
  rw [mul_comm]
end
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℂ R]
private lemma bool_snoc_sum {M : Type*} [AddCommMonoid M] (m : ℕ) (f : (Fin (m+1) → Bool) → M) :
    (∑ a, f a)=(∑ a : Fin m → Bool, f (Fin.snoc a true))+
      (∑ a : Fin m → Bool, f (Fin.snoc a false)) := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (m+1) => Bool)).sum_comp f]
  rw [Fintype.sum_prod_type,Fintype.sum_bool]
  rfl
private def monomialMap (g : ℕ → R) : (m : ℕ) → (Fin m → Bool) → (R →ₗ[ℂ] R)
  | 0, _ => LinearMap.id
  | m+1, a => (monomialMap g m (Fin.init a)).comp
      (if a (Fin.last m) then (LinearMap.mulLeftRight ℂ (g m, g m)) else LinearMap.id)
private lemma monomialMap_sum (g : ℕ → R) (m : ℕ) (X : R) :
    (∑ a : Fin m → Bool, monomialMap g m a X)=(2:ℂ)^m • finiteTwirl g m X := by
  classical
  induction m generalizing X with
  | zero => simp [monomialMap,finiteTwirl]
  | succ m ih =>
    rw [bool_snoc_sum]
    simp only [monomialMap,Fin.init_snoc,Fin.snoc_last,Bool.false_eq_true,↓reduceIte,LinearMap.comp_apply,
      LinearMap.id_apply,LinearMap.id_coe,id_eq,LinearMap.mulLeftRight_apply,LinearMap.coe_mk,AddHom.coe_mk]
    rw [ih,ih,finiteTwirl_step,pow_succ,smul_smul]
    module
private def monomialLabel (flip : ℕ → Bool) : (m : ℕ) → (Fin m → Bool) → Bool
  | 0, _ => true
  | m+1, a => if a (Fin.last m) && flip m then !(monomialLabel flip m (Fin.init a))
      else monomialLabel flip m (Fin.init a)
private lemma outcomeSign_not (b : Bool) : outcomeSign (!b)= -outcomeSign b := by cases b <;> simp [outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign]
private lemma monomialMap_push (g : ℕ → R) (flip : ℕ → Bool) (B : R) (m : ℕ)
    (hrel : ∀ l, l < m → g l*B=(if flip l then (-1:ℂ) else 1) • (B*g l))
    (a : Fin m → Bool) (X : R) :
    monomialMap g m a (B*X)=outcomeSign (monomialLabel flip m a) • (B*monomialMap g m a X) := by
  induction m generalizing X with
  | zero => simp [monomialMap,monomialLabel,outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign]
  | succ m ih =>
    have hi := ih (fun l hl => hrel l (by omega)) (Fin.init a)
    have he : g m*(B*X)*g m=(if flip m then (-1:ℂ) else 1) • (B*(g m*X*g m)) := by
      rw [← mul_assoc (g m),hrel m (by omega),smul_mul_assoc,smul_mul_assoc]
      simp only [mul_assoc]
    cases ha : a (Fin.last m) with
    | false => simpa [monomialMap,monomialLabel,ha] using hi X
    | true =>
      simp only [monomialMap,monomialLabel,ha,Bool.true_and,↓reduceIte,LinearMap.comp_apply,
        LinearMap.mulLeftRight_apply,LinearMap.coe_mk,AddHom.coe_mk]
      rw [he,map_smul,hi]
      cases hf : flip m <;> simp [hf,outcomeSign_not,smul_smul]
private lemma monomial_signed_sum (g : ℕ → R) (flip : ℕ → Bool) (B : R) (m : ℕ)
    (hB : B*B=1)
    (hrel : ∀ l, l < m → g l*B=(if flip l then (-1:ℂ) else 1) • (B*g l)) (X : R) :
    (∑ a : Fin m → Bool, outcomeSign (monomialLabel flip m a) • monomialMap g m a X)=
      (2:ℂ)^m • (B*finiteTwirl g m (B*X)) := by
  classical
  have he : ∀ a : Fin m → Bool, outcomeSign (monomialLabel flip m a) • monomialMap g m a X=
      B*monomialMap g m a (B*X) := by
    intro a
    rw [monomialMap_push g flip B m hrel,mul_smul_comm,← mul_assoc,hB,one_mul]
  simp_rw [he]
  rw [← Finset.mul_sum,monomialMap_sum,mul_smul_comm]
end
noncomputable section
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private lemma monomialMap_psd (g : ℕ → Matrix ι ι ℂ) (m : ℕ)
    (hg : ∀ l, l < m → star (g l)=g l)
    (a : Fin m → Bool) (P : Matrix ι ι ℂ) (hP : P.PosSemidef) :
    (monomialMap g m a P).PosSemidef := by
  induction m generalizing P with
  | zero => exact hP
  | succ m ih =>
    dsimp only [monomialMap,LinearMap.comp_apply]
    apply ih (fun l hl => hg l (by omega)) (Fin.init a)
    split_ifs
    · change (g m*P*g m).PosSemidef
      have hc := hP.conjTranspose_mul_mul_same (g m)
      rwa [← Matrix.star_eq_conjTranspose,hg m (by omega)] at hc
    · exact hP
private lemma normalized_monomial_parent {m q : ℕ} (g : ℕ → Matrix ι ι ℂ)
    (hg : ∀ l, l < m → star (g l)=g l) (P : Matrix ι ι ℂ) (hP : P.PosSemidef)
    (p : ℝ) (hp : 0 < p) (hnorm : finiteTwirl g m P=(p:ℂ) • (1:Matrix ι ι ℂ))
    (B : Fin q → Matrix ι ι ℂ) (hsq : ∀ v, B v*B v=1)
    (flip : Fin q → ℕ → Bool)
    (hrel : ∀ v l, l < m → g l*B v=(if flip v l then (-1:ℂ) else 1) • (B v*g l))
    (t : ℝ) (hcov : ∀ v, finiteTwirl g m (B v*P)=((t*p:ℝ):ℂ) • (1:Matrix ι ι ℂ)) :
    ∃ E : (Fin m → Bool) → Matrix ι ι ℂ,
      (∀ a, (E a).PosSemidef) ∧ (∑ a, E a=1) ∧
      ∀ v, ∑ a, outcomeSign (monomialLabel (flip v) m a) • E a=(t:ℂ) • B v := by
  classical
  let c : ℝ := (2:ℝ)^m*p
  have hc : 0 < c := mul_pos (pow_pos (by norm_num) m) hp
  have hcC : (c:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  let E : (Fin m → Bool) → Matrix ι ι ℂ := fun a => ((c⁻¹:ℝ):ℂ) • monomialMap g m a P
  refine ⟨E,?_,?_,?_⟩
  · intro a
    exact (monomialMap_psd g m hg a P hP).smul (Complex.zero_le_real.mpr (le_of_lt (inv_pos.mpr hc)))
  · dsimp only [E]
    rw [← Finset.smul_sum,monomialMap_sum,hnorm,smul_smul,smul_smul]
    have he : ((c⁻¹:ℝ):ℂ)*(2:ℂ)^m*(p:ℂ)=1 := by
      have hec : (c:ℂ)=(2:ℂ)^m*(p:ℂ) := by simp only [c,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
      rw [Complex.ofReal_inv,mul_assoc,← hec,inv_mul_cancel₀ hcC]
    rw [he,one_smul]
  · intro v
    dsimp only [E]
    simp only [smul_comm (outcomeSign _) ((c⁻¹:ℝ):ℂ)]
    rw [← Finset.smul_sum,monomial_signed_sum g (flip v) (B v) m (hsq v) (hrel v),hcov v]
    simp only [mul_smul_comm,mul_one,smul_smul]
    have heR : c⁻¹*(2:ℝ)^m*(t*p)=t := by
      calc
        _ = t*(c⁻¹*((2:ℝ)^m*p)) := by ring
        _ = t*(c⁻¹*c) := by rfl
        _ = t := by rw [inv_mul_cancel₀ (ne_of_gt hc),mul_one]
    have he : ((c⁻¹:ℝ):ℂ)*(2:ℂ)^m*((t*p:ℝ):ℂ)=(t:ℂ) := by
      simpa only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat] using congrArg Complex.ofReal heR
    rw [← mul_assoc,he]
end
noncomputable section
open scoped ComplexOrder
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

end
noncomputable section
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private lemma uniform_majorana_parent {L q : ℕ} (hL : 0 < L) (g : Fin (2*L) → Matrix ι ι ℂ)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j))
    (j k : Fin q → Fin (2*L)) (hjk : ∀ v, j v ≠ k v)
    (c : Fin q → ℂ) (hc : ∀ v, c v*c v= -1) (t : ℝ)
    (hcoeff : ∀ v, c v*(4*∑ r : Fin L, star (modeCoeff L r (j v))*modeCoeff L r (k v))=(t:ℂ)) :
    ∃ E : (Fin q → Bool) → Matrix ι ι ℂ,
      (∀ a, (E a).PosSemidef) ∧ (∑ a, E a=1) ∧
      ∀ v, ∑ a, outcomeSign (a v) • E a=(t:ℂ) • (c v • (g (j v)*g (k v))) := by
  classical
  let B : Fin q → Matrix ι ι ℂ := fun v => c v • (g (j v)*g (k v))
  let p : ℝ := (1/2:ℝ)^L
  let flip : Fin q → ℕ → Bool := fun v l => decide (l=(j v).val ∨ l=(k v).val)
  have hv := fourierVacuum_properties hL g hsq hg hanti
  have hnorm : finiteTwirl (totalGamma g) (2*L) (fourierVacuum g)=(p:ℂ) • (1:Matrix ι ι ℂ) := by
    simpa only [cliffordAverage,p,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hv.2.2.2
  have hnorm' : cliffordAverage g (fourierVacuum g)=(p:ℂ) • (1:Matrix ι ι ℂ) := hnorm
  have hcov : ∀ v, finiteTwirl (totalGamma g) (2*L) (B v*fourierVacuum g)=
      ((t*p:ℝ):ℂ) • (1:Matrix ι ι ℂ) := by
    intro v
    change cliffordAverage g (B v*fourierVacuum g)=_
    dsimp only [B]
    rw [smul_mul_assoc,map_smul,fourierVacuum_covariance hL g hsq hg hanti,hnorm']
    have he := congrArg (fun z : ℂ => (z*(p:ℂ)) • (1:Matrix ι ι ℂ)) (hcoeff v)
    simpa only [smul_smul,Complex.ofReal_mul,mul_assoc] using he
  obtain ⟨P,hP,hsum,hsigned⟩ := normalized_monomial_parent (totalGamma g)
    (m:=2*L) (by intro l hl; simpa [totalGamma,hl] using hg ⟨l,hl⟩)
    (fourierVacuum g) (fourierVacuum_psd hL g hsq hg hanti) p (by dsimp [p];positivity)
    hnorm B (fun v => imaginary_bond_square g hsq hanti (j v) (k v) (hjk v) (c v) (hc v))
    flip (by
      intro v l hl
      simpa only [totalGamma,dif_pos hl,B,flip,decide_eq_true_eq,Fin.ext_iff] using
        imaginary_bond_relation g hsq hanti (j v) (k v) ⟨l,hl⟩ (hjk v) (c v)) t hcov
  exact pushforward_signed_parent B t (fun a v => monomialLabel (flip v) (2*L) a) P hP hsum hsigned
end
noncomputable section
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def cycleCoeff (L : ℕ) (v : Fin (2*L)) : ℂ := if v.val+1 < 2*L then Complex.I else -Complex.I
def cycleMajoranaBond {L : ℕ} (g : Fin (2*L) → Matrix ι ι ℂ) (v : Fin (2*L)) : Matrix ι ι ℂ :=
  cycleCoeff L v • (g v*g (finRotate (2*L) v))
lemma cycle_majorana_parent {n : ℕ} (hn : 1 ≤ n) (g : Fin (2*(n+1)) → Matrix ι ι ℂ)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) :
    ∃ E : (Fin (2*(n+1)) → Bool) → Matrix ι ι ℂ,
      (∀ a, (E a).PosSemidef) ∧ (∑ a, E a=1) ∧
      ∀ v, ∑ a, outcomeSign (a v) • E a=(visibility n:ℂ) • cycleMajoranaBond g v := by
  have hL : 0 < n+1 := by omega
  have hrotate : ∀ v : Fin (2*(n+1)), finRotate (2*(n+1)) v =
      if hv : v.val+1 < 2*(n+1) then ⟨v.val+1,hv⟩ else ⟨0,by omega⟩ := by
    intro v
    change finRotate ((2*n+1)+1) v = _
    split_ifs with hv
    · exact finRotate_of_lt (by omega)
    · have he : v = Fin.last (2*n+1) := by
        apply Fin.ext
        simp only [Fin.val_last]
        have := v.isLt
        omega
      subst v
      exact finRotate_last'
  apply uniform_majorana_parent hL g hsq hg hanti id (finRotate (2*(n+1)))
  · intro v he
    have heval := congrArg Fin.val he
    simp only [id_eq,hrotate] at heval
    by_cases hv : v.val+1 < 2*(n+1)
    · simp only [dif_pos hv,Fin.val_mk] at heval
      omega
    · simp only [dif_neg hv,Fin.val_mk] at heval
      have := v.isLt
      omega
  · intro v
    unfold cycleCoeff
    split_ifs <;> simp [Complex.I_sq,← sq]
  · intro v
    rw [visibility_as_L]
    unfold cycleCoeff
    rw [hrotate]
    split_ifs with hv
    · simpa only [id_eq,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_natCast] using
        modeCoeff_bond hL v (⟨v.val+1,hv⟩:Fin (2*(n+1))) rfl
    · simpa only [id_eq,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_natCast] using
        modeCoeff_closing hL v (⟨0,by omega⟩:Fin (2*(n+1))) (by have := v.isLt;omega) rfl
lemma consecutive_majorana_parent {n q : ℕ} (hn : 1 ≤ n)
    (g : Fin (2*(n+1)) → Matrix ι ι ℂ)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j))
    (j k : Fin q → Fin (2*(n+1))) (hstep : ∀ v, (k v).val=(j v).val+1) :
    ∃ E : (Fin q → Bool) → Matrix ι ι ℂ,
      (∀ a, (E a).PosSemidef) ∧ (∑ a, E a=1) ∧
      ∀ v, ∑ a, outcomeSign (a v) • E a=(visibility n:ℂ) • (Complex.I • (g (j v)*g (k v))) := by
  apply uniform_majorana_parent (by omega) g hsq hg hanti j k
  · intro v
    apply Fin.ne_of_val_ne
    have := hstep v
    omega
  · intro v
    exact Complex.I_mul_I
  · intro v
    rw [visibility_as_L]
    simpa only [id_eq,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_natCast] using
      modeCoeff_bond (by omega) (j v) (k v) (hstep v)
end
end D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordBondParents
