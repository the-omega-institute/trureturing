/- GID: D5/S3/Factorization/PositiveRationalGroup
   generality: G
   mirror-B: D5/B/S3/Factorization/PositiveRationalGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Signed prime exponents give the additive presentation of positive rationals. -/

import D5.S3.Factorization.FreeCommMonoid
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.Tactic

/- Provenance: a new localization argument built on pinned mathlib's
   `AddSubmonoid.LocalizationMap.addEquivOfLocalizations` and
   `AddSubmonoid.isLocalizationMap_of_addGroup`, with the natural prime ledger
   supplied by the repository's wrapper around `PNat.factorMultisetEquiv`. -/

namespace D5.S3.Factorization.PositiveRationalGroup

/-- Finite ledgers of natural prime exponents. -/
abbrev NaturalPrimeLedger := Nat.Primes →₀ Nat

/-- Finite ledgers of signed prime exponents. -/
abbrev SignedPrimeLedger := Nat.Primes →₀ Int

/-- Positive rationals, represented by the units of the nonnegative rationals. -/
abbrev PositiveRational := NNRatˣ

noncomputable def pnatNaturalLedgerEquiv :
    Additive PNat ≃+ NaturalPrimeLedger :=
  (MulEquiv.toAdditiveLeft primeFactorMulEquiv).trans Multiset.toFinsupp

def pnatToPositiveRational : PNat →* PositiveRational where
  toFun n := Units.mk0 (n : NNRat) (by exact_mod_cast n.pos.ne')
  map_one' := by ext; simp
  map_mul' m n := by ext; simp

noncomputable def naturalLedgerToPositiveRational :
    NaturalPrimeLedger →+ Additive PositiveRational :=
  (MonoidHom.toAdditive pnatToPositiveRational).comp
    pnatNaturalLedgerEquiv.symm.toAddMonoidHom

noncomputable def naturalLedgerCast : NaturalPrimeLedger →+ SignedPrimeLedger :=
  Finsupp.mapRange.addMonoidHom Int.ofNatHom

private theorem naturalLedgerCast_injective :
    Function.Injective naturalLedgerCast := by
  intro x y h
  ext p
  have hp := DFunLike.congr_fun h p
  exact Int.ofNat_inj.mp hp

private theorem naturalLedgerCast_surj_fraction (z : SignedPrimeLedger) :
    ∃ x : NaturalPrimeLedger, ∃ y ∈ (⊤ : AddSubmonoid NaturalPrimeLedger),
      z = naturalLedgerCast x - naturalLedgerCast y := by
  let pos : NaturalPrimeLedger := z.mapRange Int.toNat Int.toNat_zero
  let neg : NaturalPrimeLedger := (-z).mapRange Int.toNat Int.toNat_zero
  refine ⟨pos, neg, by simp, ?_⟩
  ext p
  simp [naturalLedgerCast, pos, neg]

private theorem naturalLedgerToPositiveRational_injective :
    Function.Injective naturalLedgerToPositiveRational := by
  intro x y h
  apply pnatNaturalLedgerEquiv.symm.injective
  apply Additive.toMul.injective
  apply PNat.coe_injective
  change Additive.ofMul (pnatToPositiveRational
    (pnatNaturalLedgerEquiv.symm x).toMul) =
      Additive.ofMul (pnatToPositiveRational
        (pnatNaturalLedgerEquiv.symm y).toMul) at h
  have h' := congrArg Additive.toMul h
  have hval := congrArg (fun q : PositiveRational => (q : NNRat)) h'
  change ((((pnatNaturalLedgerEquiv.symm x).toMul : PNat) : Nat) : NNRat) =
    ((((pnatNaturalLedgerEquiv.symm y).toMul : PNat) : Nat) : NNRat) at hval
  exact_mod_cast hval

private theorem naturalLedgerToPositiveRational_surj_fraction
    (q : Additive PositiveRational) :
    ∃ x : NaturalPrimeLedger, ∃ y ∈ (⊤ : AddSubmonoid NaturalPrimeLedger),
      q = naturalLedgerToPositiveRational x - naturalLedgerToPositiveRational y := by
  let num : PNat := ⟨(q.toMul : NNRat).num,
    NNRat.num_pos.mpr (pos_iff_ne_zero.mpr q.toMul.ne_zero)⟩
  let den : PNat := ⟨(q.toMul : NNRat).den, (q.toMul : NNRat).den_pos⟩
  refine ⟨pnatNaturalLedgerEquiv (Additive.ofMul num),
    pnatNaturalLedgerEquiv (Additive.ofMul den), by simp, ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  simp [naturalLedgerToPositiveRational, pnatToPositiveRational, num, den,
    (q.toMul : NNRat).num_div_den]

noncomputable def signedLedgerLocalization :
    (⊤ : AddSubmonoid NaturalPrimeLedger).LocalizationMap SignedPrimeLedger where
  __ := naturalLedgerCast
  isLocalizationMap :=
    AddSubmonoid.isLocalizationMap_of_addGroup
      naturalLedgerCast_injective naturalLedgerCast_surj_fraction

noncomputable def positiveRationalLocalization :
    (⊤ : AddSubmonoid NaturalPrimeLedger).LocalizationMap
      (Additive PositiveRational) where
  __ := naturalLedgerToPositiveRational
  isLocalizationMap :=
    AddSubmonoid.isLocalizationMap_of_addGroup
      naturalLedgerToPositiveRational_injective
      naturalLedgerToPositiveRational_surj_fraction

/-- The canonical equivalence between signed prime ledgers and positive rationals. -/
noncomputable def primeExponentEquivPositiveRational :
    SignedPrimeLedger ≃+ Additive PositiveRational :=
  signedLedgerLocalization.addEquivOfLocalizations positiveRationalLocalization

/-- Finite signed prime exponents and positive rationals are isomorphic groups. -/
theorem signed_prime_ledger_equiv_positive_rationals :
    Function.Bijective primeExponentEquivPositiveRational :=
  primeExponentEquivPositiveRational.bijective

/-- Natural logarithm transported through the positive-rational equivalence. -/
noncomputable def rationalLogLength (a : SignedPrimeLedger) : Real :=
  Real.log (((((primeExponentEquivPositiveRational a).toMul : NNRat) : Rat) : Real))

/-- Transported logarithmic length converts ledger addition into real addition. -/
theorem rational_log_length_add (a b : SignedPrimeLedger) :
    rationalLogLength (a + b) = rationalLogLength a + rationalLogLength b := by
  rw [rationalLogLength, rationalLogLength, rationalLogLength,
    map_add primeExponentEquivPositiveRational]
  rw [toMul_add]
  simp only [Units.val_mul, NNRat.coe_mul, Rat.cast_mul]
  apply Real.log_mul
  · exact_mod_cast (primeExponentEquivPositiveRational a).toMul.ne_zero
  · exact_mod_cast (primeExponentEquivPositiveRational b).toMul.ne_zero

/-- Signed coordinates make the transported logarithmic length genuinely negative. -/
theorem exists_negative_rational_log_length :
    ∃ a : SignedPrimeLedger, rationalLogLength a < 0 := by
  let half : PositiveRational := Units.mk0 ((1 : NNRat) / 2) (by norm_num)
  refine ⟨primeExponentEquivPositiveRational.symm (Additive.ofMul half), ?_⟩
  rw [rationalLogLength, primeExponentEquivPositiveRational.apply_symm_apply]
  exact Real.log_neg (by norm_num [half]) (by norm_num [half])

end D5.S3.Factorization.PositiveRationalGroup
