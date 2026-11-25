/- GID: D5/S3/Calculus/DFiniteCompose
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Composition and the formal chain rule for rational coefficient streams. -/

module
prelude
import all OmegaInit.Prelude
public import D5.S3.Calculus.DFiniteJet.Cayley
public import D5.S3.Calculus.DFiniteJet.Identities
import D5.S0.Arithmetic.Euclidean.Division

/-!
Omega original.

Composition of rational coefficient streams, the formal chain rule, and the
Cayley formulas for the sine and cosine of twice the formal arctangent.
-/

noncomputable section

@[expose] public section

namespace Omega.JetSeq

/-- The natural power of a series under the Cauchy product. -/
def power (g : JetSeq) (k : Nat) : JetSeq :=
  Nat.rec one (fun _ p => mul p g) k

/-- Sum the first `terms` outer coefficients times the corresponding powers of the inner series. -/
def partialCompose (f g : JetSeq) (terms : Nat) : JetSeq :=
  Nat.rec zero (fun k sum => add sum (smul (f k) (power g k))) terms

/-- Coefficient `n` of the composite uses the terms `f(k) * g^k` for `k ≤ n`.
For an inner series with zero constant coefficient these are all the contributing terms. -/
def compose (f g : JetSeq) : JetSeq := fun n => partialCompose f g n.succ n

/-- The constant coefficient of a composite with zero inner constant coefficient. -/
theorem compose_zero_at (f g : JetSeq)
    (_g0 : IntRatio.Equivalent (g Nat.zero) IntRatio.zero) :
    IntRatio.Equivalent (compose f g Nat.zero) (f Nat.zero) :=
  (IntRatio.add_comm _ _).trans ((IntRatio.add_zero _).trans (IntRatio.mul_one _))

private theorem finite_power {g : JetSeq} (hg : Finite g) (k : Nat) : Finite (power g k) :=
  Nat.rec (motive := fun i => Finite (power g i)) finite_one (fun _ ih => finite_mul ih hg) k

private theorem finite_mul_zero_prefix {f g : JetSeq} (hg : Finite g) (n : Nat)
    (vanishes : ∀ i, Nat.le i n → IntRatio.Equivalent (f i) IntRatio.zero) :
    IntRatio.Equivalent (mul f g n) IntRatio.zero :=
  (Nat.rec (motive := fun n => ∀ f : JetSeq,
    (∀ i, Nat.le i n → IntRatio.Equivalent (f i) IntRatio.zero) →
    IntRatio.Equivalent (mul f g n) IntRatio.zero)
    (fun _ h => (IntRatio.mul_congr_left (h Nat.zero (Nat.zero_le _)) _).trans
      (IntRatio.zero_mul (hg Nat.zero)))
    (fun n ih f h =>
      (IntRatio.add_congr
        ((IntRatio.mul_congr_left (h Nat.zero (Nat.zero_le _)) _).trans (IntRatio.zero_mul (hg n.succ)))
        (ih (tail f) (fun i hi => h i.succ (Nat.succ_le_succ hi)))).trans
        (IntRatio.add_zero IntRatio.zero)) n) f vanishes

private theorem power_vanishes {g : JetSeq} (hg : Finite g)
    (g0 : IntRatio.Equivalent (g Nat.zero) IntRatio.zero) (k n : Nat) (hn : Nat.lt n k) :
    IntRatio.Equivalent (power g k n) IntRatio.zero :=
  (Nat.rec (motive := fun k => ∀ n, Nat.lt n k →
    IntRatio.Equivalent (power g k n) IntRatio.zero)
    (fun n h => False.elim (Nat.not_succ_le_zero n h))
    (fun k ih n =>
      Nat.rec (motive := fun n => Nat.lt n k.succ →
        IntRatio.Equivalent (power g k.succ n) IntRatio.zero)
        (fun _ => (IntRatio.mul_congr (IntRatio.equivalent_refl _) g0).trans
          (IntRatio.mul_zero (finite_power hg k Nat.zero)))
        (fun j _ hj =>
          have lower := finite_mul_zero_prefix (f := power g k) (g := tail g)
            (fun i => hg i.succ) j (fun i hi => ih i (Nat.le_trans (Nat.succ_le_succ hi) (Nat.le_of_succ_le_succ hj)))
          have last := (IntRatio.mul_congr (IntRatio.equivalent_refl _) g0).trans
            (IntRatio.mul_zero (finite_power hg k j.succ))
          (mul_succ_right (power g k) g j).trans
            ((IntRatio.add_congr lower last).trans (IntRatio.add_zero IntRatio.zero))) n) k) n hn

/-- Every cutoff beyond the coefficient degree gives the same coefficient. -/
private theorem partial_agrees {f g : JetSeq} (hf : Finite f) (hg : Finite g)
    (g0 : IntRatio.Equivalent (g Nat.zero) IntRatio.zero) (terms n : Nat) (h : Nat.lt n terms) :
    IntRatio.Equivalent (partialCompose f g terms n) (compose f g n) :=
  (Nat.rec (motive := fun k => ∀ n, Nat.lt n k →
    IntRatio.Equivalent (partialCompose f g k n) (compose f g n))
    (fun n h => False.elim (Nat.not_succ_le_zero n h))
    (fun k ih n h =>
      (Arithmetic.le_or_lt k n).elim
        (fun hk => Eq.subst (motive := fun t : Nat => IntRatio.Equivalent (partialCompose f g t.succ n) (compose f g n))
          (Nat.le_antisymm hk (Nat.le_of_succ_le_succ h)).symm (IntRatio.equivalent_refl (compose f g n)))
        (fun hn =>
          have extra := (IntRatio.mul_congr (IntRatio.equivalent_refl _)
            (power_vanishes hg g0 k n hn)).trans (IntRatio.mul_zero (hf k))
          (IntRatio.add_congr (ih n hn) extra).trans (IntRatio.add_zero _))) terms) n h

private theorem ofNat_succ_smul (k : Nat) (f : JetSeq) :
    Equivalent (add (smul (IntRatio.ofNat k) f) f) (smul (IntRatio.ofNat k.succ) f) :=
  fun n =>
    have expand := (IntRatio.add_mul (IntRatio.ofNat k) IntRatio.one (f n)).trans
      (IntRatio.add_congr (IntRatio.equivalent_refl _) (IntRatio.one_mul (f n)))
    Eq.subst (motive := fun a : IntRatio => IntRatio.Equivalent (add (smul (IntRatio.ofNat k) f) f n) (a.mul (f n)))
      ((IntRatio.ofNat_add k Nat.one).trans (congrArg IntRatio.ofNat (Nat.add_one k))) expand.symm

private theorem deriv_power {g : JetSeq} (hg : Finite g) (k : Nat) :
    Equivalent (deriv (power g k.succ))
      (mul (smul (IntRatio.ofNat k.succ) (power g k)) (deriv g)) :=
  Nat.rec (motive := fun k => Equivalent (deriv (power g k.succ))
    (mul (smul (IntRatio.ofNat k.succ) (power g k)) (deriv g)))
    ((deriv_congr (one_mul hg)).trans
      ((mul_congr (fun n => IntRatio.one_mul (one n)) (equivalent_refl (deriv g))).trans
        (one_mul (finite_deriv hg))).symm)
    (fun k ih =>
      let weight := IntRatio.ofNat k.succ
      let p := power g k
      let next := power g k.succ
      let dg := deriv g
      have commute : Equivalent (mul (mul (smul weight p) dg) g)
          (mul (smul weight next) dg) :=
        (mul_assoc (smul weight p) dg g).trans
          ((mul_congr (equivalent_refl _) (mul_comm dg g)).trans
            ((mul_assoc (smul weight p) g dg).symm.trans
              (mul_congr (smul_mul weight p g) (equivalent_refl dg))))
      (deriv_mul next g).trans
        ((add_congr ((mul_congr ih (equivalent_refl g)).trans commute) (equivalent_refl _)).trans
          ((add_mul (smul weight next) next dg).symm.trans
            (mul_congr (ofNat_succ_smul k.succ next) (equivalent_refl dg))))) k

/-- Differentiating a finite substitution reduces its outer cutoff by one. -/
private theorem deriv_partial {f g : JetSeq} (hf : Finite f) (hg : Finite g) (k : Nat) :
    Equivalent (deriv (partialCompose f g k.succ))
      (mul (partialCompose (deriv f) g k) (deriv g)) :=
  Nat.rec (motive := fun k => Equivalent (deriv (partialCompose f g k.succ))
    (mul (partialCompose (deriv f) g k) (deriv g)))
    (fun n =>
      have d0 : IntRatio.Equivalent (deriv zero n) IntRatio.zero :=
        IntRatio.mul_zero (IntRatio.finite_ofNat n.succ)
      have constantDeriv : IntRatio.Equivalent (deriv (smul (f Nat.zero) one) n) IntRatio.zero :=
        (IntRatio.mul_congr (IntRatio.equivalent_refl _) (IntRatio.mul_zero (hf Nat.zero))).trans d0
      (deriv_add zero (smul (f Nat.zero) one) n).trans
        ((IntRatio.add_congr d0 constantDeriv).trans
          ((IntRatio.add_zero IntRatio.zero).trans (zero_mul (finite_deriv hg) n).symm)))
    (fun k ih =>
      let p := power g k
      let dg := deriv g
      let c := f k.succ
      let weight := IntRatio.ofNat k.succ
      have term : Equivalent (deriv (smul c (power g k.succ)))
          (mul (smul (deriv f k) p) dg) :=
        (deriv_smul c (power g k.succ)).trans
          ((smul_congr (IntRatio.equivalent_refl c) (deriv_power hg k)).trans
            ((smul_mul c (smul weight p) dg).symm.trans
              (mul_congr
                (fun n => (IntRatio.mul_assoc c weight (p n)).symm.trans
                  (IntRatio.mul_congr_left (IntRatio.mul_comm c weight) (p n)))
                (equivalent_refl dg))))
      (deriv_add (partialCompose f g k.succ) (smul c (power g k.succ))).trans
        ((add_congr ih term).trans (add_mul _ _ dg).symm)) k

/-- The formal chain rule holds through every degree of the composite derivative. -/
theorem deriv_compose_equivAt (N : Nat) (f g : JetSeq) (hf : Finite f) (hg : Finite g)
    (g0 : IntRatio.Equivalent (g Nat.zero) IntRatio.zero) :
    EquivalentAt N (deriv (compose f g)) (mul (compose (deriv f) g) (deriv g)) :=
  fun n _ =>
    have left := IntRatio.mul_congr (IntRatio.equivalent_refl (IntRatio.ofNat n.succ))
      (partial_agrees hf hg g0 n.succ.succ n.succ (Nat.le_refl _)).symm
    have right : EquivalentAt n (partialCompose (deriv f) g n.succ) (compose (deriv f) g) :=
      fun j hj => partial_agrees (finite_deriv hf) hg g0 n.succ j (Nat.succ_le_succ hj)
    left.trans ((deriv_partial hf hg n.succ n).trans
      (mul_congr_at n right ((equivalent_refl (deriv g)).at n) n (Nat.le_refl n)))

private theorem compose_congr_outer {f h : JetSeq} (g : JetSeq) (same : Equivalent f h) :
    Equivalent (compose f g) (compose h g) :=
  have agree := Nat.rec (motive := fun k => Equivalent (partialCompose f g k) (partialCompose h g k))
    (equivalent_refl zero) (fun k ih => add_congr ih
      (smul_congr (same k) (equivalent_refl (power g k))))
  fun n => agree n.succ n

private theorem compose_neg (f g : JetSeq) :
    Equivalent (compose (neg f) g) (neg (compose f g)) :=
  have agree := Nat.rec (motive := fun k =>
      Equivalent (partialCompose (neg f) g k) (neg (partialCompose f g k)))
    (equivalent_refl zero)
    (fun k ih n =>
      (IntRatio.add_congr (ih n) (IntRatio.neg_mul (f k) (power g k n))).trans
        (IntRatio.neg_add (partialCompose f g k n) (smul (f k) (power g k) n)).symm)
  fun n => agree n.succ n

private def twoAtan : JetSeq := smul IntRatio.two Atan

private theorem twoAtan_zero : IntRatio.Equivalent (twoAtan Nat.zero) IntRatio.zero :=
  IntRatio.mul_zero (x := IntRatio.two) True.intro

private theorem twoAtan_ode :
    Equivalent (mul (deriv twoAtan) oneAddEtaSq) (smul IntRatio.two one) :=
  (mul_congr (deriv_smul IntRatio.two Atan) (equivalent_refl oneAddEtaSq)).trans
    ((smul_mul IntRatio.two (deriv Atan) oneAddEtaSq).trans
      (smul_congr (IntRatio.equivalent_refl _) atan_ode))

private theorem clear_twoAtan_derivative (f : JetSeq) (hf : Finite f) :
    Equivalent (mul (deriv (compose f twoAtan)) oneAddEtaSq)
      (smul IntRatio.two (compose (deriv f) twoAtan)) :=
  let u := compose (deriv f) twoAtan
  have chain : Equivalent (deriv (compose f twoAtan)) (mul u (deriv twoAtan)) :=
    fun n => deriv_compose_equivAt n f twoAtan hf (finite_smul (a := IntRatio.two) True.intro atan_finite)
      twoAtan_zero n (Nat.le_refl n)
  have finiteU : Finite u :=
    fun n => (Nat.rec (motive := fun k => Finite (partialCompose (deriv f) twoAtan k))
      finite_zero (fun k ih => finite_add ih
        (finite_smul (finite_deriv hf k) (finite_power (finite_smul (a := IntRatio.two) True.intro atan_finite) k))) n.succ) n
  (mul_congr chain (equivalent_refl oneAddEtaSq)).trans
    ((mul_assoc u (deriv twoAtan) oneAddEtaSq).trans
      ((mul_congr (equivalent_refl u) twoAtan_ode).trans
        ((mul_smul IntRatio.two u one).trans
          (smul_congr (IntRatio.equivalent_refl _) (mul_one finiteU)))))

private theorem twoAtan_cayley (N : Nat) :
    And (EquivalentAt N (compose Cos twoAtan) CayleyCos)
      (EquivalentAt N (compose Sin twoAtan) CayleySin) :=
  have cosODE := (clear_twoAtan_derivative Cos cos_finite).trans
    ((smul_congr (IntRatio.equivalent_refl _)
      ((compose_congr_outer twoAtan deriv_cos).trans (compose_neg Sin twoAtan))).trans
      (fun n => (IntRatio.mul_neg IntRatio.two (compose Sin twoAtan n)).trans
        (IntRatio.neg_mul IntRatio.two (compose Sin twoAtan n)).symm))
  have sinODE := (clear_twoAtan_derivative Sin sin_finite).trans
    (smul_congr (IntRatio.equivalent_refl _) (compose_congr_outer twoAtan deriv_sin))
  cayley_unique_at N (compose_zero_at Cos twoAtan twoAtan_zero)
    (compose_zero_at Sin twoAtan twoAtan_zero) (fun n _ => cosODE n) (fun n _ => sinODE n)

/-- The cosine of twice the formal arctangent is the Cayley cosine. -/
theorem cos_two_atan_eq_cayley (N : Nat) :
    EquivalentAt N (compose Cos (smul IntRatio.two Atan)) CayleyCos :=
  (twoAtan_cayley N).left

/-- The sine of twice the formal arctangent is the Cayley sine. -/
theorem sin_two_atan_eq_cayley (N : Nat) :
    EquivalentAt N (compose Sin (smul IntRatio.two Atan)) CayleySin :=
  (twoAtan_cayley N).right

end Omega.JetSeq
