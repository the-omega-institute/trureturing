/- GID: D5/S3/Factorization/ProfinitePrimeDecomposition
   generality: G
   mirror-B: D5/B/S3/Factorization/ProfinitePrimeDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible residues decompose bijectively into all prime-adic integer coordinates. -/

import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Padics.RingHoms

/- Provenance: new assembly over pinned mathlib's finite CRT equivalence
   (`ZMod.equivPi`) and prime-adic residue maps (`PadicInt.toZModPow`,
   `PadicInt.cast_toZModPow`, `PadicInt.ext_of_toZModPow`). -/

namespace D5.S3.Factorization.ProfinitePrimeDecomposition

/-- A profinite integer is a residue modulo every positive natural number,
compatible with reduction along divisibility. -/
abbrev ProfiniteIntegers :=
  {x : ∀ n : ℕ+, ZMod n.1 //
    ∀ (m n : ℕ+), m.1 ∣ n.1 → ZMod.cast (x n) = x m}

private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private def primeApproximation
    (x : ProfiniteIntegers) (p : Nat.Primes) (n : ℕ) : ℤ :=
  letI : NeZero (p.1 ^ n) := ⟨pow_ne_zero _ p.2.ne_zero⟩
  (x.1 ⟨p.1 ^ n, pow_pos p.2.pos n⟩).val

private theorem primeApproximation_compatible
    (x : ProfiniteIntegers) (p : Nat.Primes) (i : ℕ) :
    (p.1 : ℤ) ^ i ∣ primeApproximation x p (i + 1) - primeApproximation x p i := by
  let lower : ℕ+ := ⟨p.1 ^ i, pow_pos p.2.pos i⟩
  let upper : ℕ+ := ⟨p.1 ^ (i + 1), pow_pos p.2.pos (i + 1)⟩
  have hcompat := x.2 lower upper (pow_dvd_pow p.1 (Nat.le_succ i))
  rw [← Int.natCast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
  simpa [primeApproximation, lower, upper, ZMod.natCast_val] using
    sub_eq_zero.mpr hcompat

/-- Project a compatible residue family to its coordinate at a prime. -/
noncomputable def primeProjection
    (x : ProfiniteIntegers) (p : Nat.Primes) : ℤ_[p.1] :=
  PadicInt.ofIntSeq (primeApproximation x p)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (primeApproximation x p) p.1
      (fun i ↦ primeApproximation_compatible x p i))

private theorem primeProjection_mod
    (x : ProfiniteIntegers) (p : Nat.Primes) (n : ℕ) :
    PadicInt.toZModPow n (primeProjection x p) =
      x.1 ⟨p.1 ^ n, pow_pos p.2.pos n⟩ := by
  rw [primeProjection,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (primeApproximation x p) p.1
      (fun i ↦ primeApproximation_compatible x p i) n]
  simp [primeApproximation]

private theorem equivPi_apply {n : ℕ} (hn : n ≠ 0) (x : ZMod n)
    (p : n.primeFactors) :
    (ZMod.equivPi n hn x) p = ZMod.cast x := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast]
  change (k : ZMod (p.1 ^ n.factorization p.1)) = ZMod.cast (k : ZMod n)
  exact (map_intCast (ZMod.castHom (by
    exact ((Nat.prime_of_mem_primeFactors p.2).pow_dvd_iff_le_factorization hn).2
      le_rfl) (ZMod (p.1 ^ n.factorization p.1))) k).symm

private theorem cast_cast {a b c : ℕ}
    (hba : b ∣ a) (hcb : c ∣ b) (x : ZMod a) :
    (ZMod.cast (ZMod.cast x : ZMod b) : ZMod c) = ZMod.cast x := by
  change (ZMod.castHom hcb (ZMod c)) ((ZMod.castHom hba (ZMod b)) x) =
    (ZMod.castHom (hcb.trans hba) (ZMod c)) x
  exact DFunLike.congr_fun (ZMod.castHom_comp hcb hba) x

private noncomputable def primeFactorResidues
    (y : ∀ p : Nat.Primes, ℤ_[p.1]) (n : ℕ+) :
    ∀ q : n.1.primeFactors, ZMod (q.1 ^ n.1.factorization q.1) := fun q ↦
  let hp := Nat.prime_of_mem_primeFactors q.2
  letI : Fact q.1.Prime := ⟨hp⟩
  let p : Nat.Primes := ⟨q.1, hp⟩
  PadicInt.toZModPow (n.1.factorization q.1) (y p)

private noncomputable def assembleResidue
    (y : ∀ p : Nat.Primes, ℤ_[p.1]) (n : ℕ+) : ZMod n.1 :=
  (ZMod.equivPi n.1 n.2.ne').symm (primeFactorResidues y n)

private theorem assembleResidue_compatible
    (y : ∀ p : Nat.Primes, ℤ_[p.1]) (m n : ℕ+) (h : m.1 ∣ n.1) :
    ZMod.cast (assembleResidue y n) = assembleResidue y m := by
  apply (ZMod.equivPi m.1 m.2.ne').injective
  funext q
  let hp := Nat.prime_of_mem_primeFactors q.2
  letI : Fact q.1.Prime := ⟨hp⟩
  rw [equivPi_apply]
  simp only [assembleResidue, RingEquiv.apply_symm_apply]
  let qn : n.1.primeFactors := ⟨q.1, Nat.mem_primeFactors.mpr ⟨
    Nat.prime_of_mem_primeFactors q.2,
    (Nat.dvd_of_mem_primeFactors q.2).trans h,
    n.2.ne'⟩⟩
  have hcomponent := congrFun
    ((ZMod.equivPi n.1 n.2.ne').apply_symm_apply (primeFactorResidues y n)) qn
  rw [equivPi_apply] at hcomponent
  have hfac : m.1.factorization q.1 ≤ n.1.factorization q.1 :=
    ((Nat.factorization_le_iff_dvd m.2.ne' n.2.ne').2 h) q.1
  have hfactorM : q.1 ^ m.1.factorization q.1 ∣ m.1 :=
    (hp.pow_dvd_iff_le_factorization m.2.ne').2 le_rfl
  have hfactorN : q.1 ^ n.1.factorization q.1 ∣ n.1 :=
    (hp.pow_dvd_iff_le_factorization n.2.ne').2 le_rfl
  have hcomponent' :
      (ZMod.cast (assembleResidue y n) :
          ZMod (q.1 ^ n.1.factorization q.1)) =
        PadicInt.toZModPow (n.1.factorization q.1) (y ⟨q.1, hp⟩) := by
    simpa [assembleResidue, primeFactorResidues, qn] using hcomponent
  calc
    (ZMod.cast (ZMod.cast (assembleResidue y n) : ZMod m.1) :
        ZMod (q.1 ^ m.1.factorization q.1)) =
        (ZMod.cast (assembleResidue y n) :
          ZMod (q.1 ^ m.1.factorization q.1)) :=
      cast_cast h hfactorM _
    _ = ZMod.cast
        (ZMod.cast (assembleResidue y n) :
          ZMod (q.1 ^ n.1.factorization q.1)) :=
      (cast_cast hfactorN (pow_dvd_pow q.1 hfac) _).symm
    _ = ZMod.cast
        (PadicInt.toZModPow (n.1.factorization q.1) (y ⟨q.1, hp⟩)) :=
      congrArg ZMod.cast hcomponent'
    _ = PadicInt.toZModPow (m.1.factorization q.1) (y ⟨q.1, hp⟩) :=
      PadicInt.cast_toZModPow _ _ hfac _

/-- Assemble a compatible residue family from all of its prime-adic
coordinates by finite Chinese remaindering at each modulus. -/
noncomputable def assemble
    (y : ∀ p : Nat.Primes, ℤ_[p.1]) : ProfiniteIntegers :=
  ⟨assembleResidue y, assembleResidue_compatible y⟩

/-- Simultaneously project a profinite integer to every prime-adic factor. -/
noncomputable def primeProjectionFamily
    (x : ProfiniteIntegers) : ∀ p : Nat.Primes, ℤ_[p.1] :=
  fun p ↦ primeProjection x p

private theorem assemble_primeProjectionFamily (x : ProfiniteIntegers) :
    assemble (primeProjectionFamily x) = x := by
  apply Subtype.ext
  funext n
  apply (ZMod.equivPi n.1 n.2.ne').injective
  funext q
  simp only [assemble]
  rw [show (ZMod.equivPi n.1 n.2.ne')
        (assembleResidue (primeProjectionFamily x) n) =
        primeFactorResidues (primeProjectionFamily x) n by
      exact (ZMod.equivPi n.1 n.2.ne').apply_symm_apply
        (primeFactorResidues (primeProjectionFamily x) n),
    equivPi_apply]
  let hp := Nat.prime_of_mem_primeFactors q.2
  letI : Fact q.1.Prime := ⟨hp⟩
  let factor : ℕ+ :=
    ⟨q.1 ^ n.1.factorization q.1, pow_pos hp.pos (n.1.factorization q.1)⟩
  have hfactor : factor.1 ∣ n.1 :=
    (hp.pow_dvd_iff_le_factorization n.2.ne').2 le_rfl
  change PadicInt.toZModPow (n.1.factorization q.1)
      (primeProjection x ⟨q.1, hp⟩) = ZMod.cast (x.1 n)
  rw [primeProjection_mod]
  exact (x.2 factor n hfactor).symm

private theorem primeProjectionFamily_assemble
    (y : ∀ p : Nat.Primes, ℤ_[p.1]) :
    primeProjectionFamily (assemble y) = y := by
  funext p
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  simp only [primeProjectionFamily]
  rw [primeProjection_mod]
  simp only [assemble]
  cases k with
  | zero =>
      change assembleResidue y (⟨1, Nat.zero_lt_one⟩ : ℕ+) =
        PadicInt.toZModPow 0 (y p)
      exact Subsingleton.elim _ _
  | succ k =>
      let n : ℕ+ := ⟨p.1 ^ (k + 1), pow_pos p.2.pos (k + 1)⟩
      change assembleResidue y n = PadicInt.toZModPow (k + 1) (y p)
      apply (ZMod.equivPi n.1 n.2.ne').injective
      funext q
      rw [show (ZMod.equivPi n.1 n.2.ne') (assembleResidue y n) =
          primeFactorResidues y n by
        exact (ZMod.equivPi n.1 n.2.ne').apply_symm_apply
          (primeFactorResidues y n),
        equivPi_apply]
      have hqprime := Nat.prime_of_mem_primeFactors q.2
      letI : Fact q.1.Prime := ⟨hqprime⟩
      have hqp : q.1 = p.1 :=
        (Nat.prime_dvd_prime_iff_eq hqprime p.2).1
          (hqprime.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors q.2))
      let qp : n.1.primeFactors := ⟨p.1, Nat.mem_primeFactors.mpr ⟨
        p.2, dvd_pow_self p.1 (Nat.succ_ne_zero k), n.2.ne'⟩⟩
      have hqeq : q = qp := Subtype.ext hqp
      subst q
      simp only [primeFactorResidues, n, qp]
      rw [Nat.factorization_pow_self p.2]
      change PadicInt.toZModPow (k + 1) (y p) =
        ZMod.cast (PadicInt.toZModPow (k + 1) (y p))
      exact (ZMod.cast_id _ _).symm

/-- The explicit equivalence between compatible residues and the product of
the prime-adic integer rings. -/
noncomputable def profinitePrimeEquiv :
    ProfiniteIntegers ≃ (∀ p : Nat.Primes, ℤ_[p.1]) where
  toFun := primeProjectionFamily
  invFun := assemble
  left_inv := assemble_primeProjectionFamily
  right_inv := primeProjectionFamily_assemble

/-- Compatible residues are classified bijectively by their complete family
of prime-adic coordinates. -/
theorem profinite_prime_decomposition :
    Function.Bijective primeProjectionFamily :=
  profinitePrimeEquiv.bijective

end D5.S3.Factorization.ProfinitePrimeDecomposition
