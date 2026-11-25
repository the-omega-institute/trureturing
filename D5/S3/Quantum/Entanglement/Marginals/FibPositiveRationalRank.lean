/- GID: D5/S3/Quantum/Entanglement/Marginals/FibPositiveRationalRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/FibPositiveRationalRank
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Positive occupation with a pure extension admits a rational rank-two bound. -/

import D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity

/-! Separate the unread double-endpoint coherences while keeping the edge marginals. -/

open Matrix Complex
open scoped Matrix ComplexOrder ComplexConjugate
open D5.S3.Quantum.Entanglement.Marginals.FibCoherentExtension
open D5.S3.Quantum.Entanglement.Marginals.FibMarginalExtension (Site Word edgeTrace)
open D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalPurity
open D5.S3.Quantum.Entanglement.Marginals.FibRationalPureExtension
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalRank

private def vacuumMiddle (ψ : Word → ℂ) : Word → ℂ
  | .inl i => if i = 0 then ψ (.inl i) else 0
  | .inr false => ψ (.inr false)
  | .inr true => 0

private def doubleEndpoint (ψ : Word → ℂ) : Word → ℂ
  | .inl _ => 0
  | .inr false => 0
  | .inr true => ψ (.inr true)

private theorem rank_two_outer {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    (rankOneDensity x + rankOneDensity y).rank ≤ 2 := by
  let M : Matrix ι (Fin 2) ℂ := fun i j => ![x i, y i] j
  have hM : M * Mᴴ = rankOneDensity x + rankOneDensity y := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp only [Matrix.conjTranspose_apply]
    simp [M, rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply]
  rw [← hM]
  exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width M)

private theorem separate_double_endpoint (b : ℝ) (u z : ℂ) (L R : Matrix Bool Bool ℂ)
    (hb : 0 < b) (qL : ∀ i j, RationalEntry (L i j)) (qu : RationalEntry u)
    (ψ : Word → ℂ) (hψ : MatchesCoherentData b L R u 0 0 z (rankOneDensity ψ)) :
    ∃ ρ : Matrix Word Word ℂ, ρ.PosSemidef ∧ MatchesCoherentData b L R u 0 0 0 ρ ∧
      ρ.rank ≤ 2 ∧ ∀ i j, RationalEntry (ρ i j) := by
  obtain ⟨ht, hL, hR, hz⟩ := hψ
  have hmid : ψ (.inl 0) * conj (ψ (.inl 0)) = (b : ℂ) := by
    have h := congrFun (congrFun hL 1) 1
    change ψ (.inl 0) * conj (ψ (.inl 0)) + 0 = (b : ℂ) at h
    simpa only [add_zero] using h
  have hmid0 : ψ (.inl 0) ≠ 0 := by
    intro h
    have he := (Complex.ofReal_ne_zero.mpr hb.ne') (by simpa [h] using hmid.symm)
    exact he
  have hzero (i : Site) (h : ψ (.inl 0) * conj (ψ (.inl i)) = 0) : ψ (.inl i) = 0 :=
    by simpa using (mul_eq_zero.mp h).resolve_left hmid0
  have h1 : ψ (.inl 1) = 0 := by
    apply hzero
    have h := congrFun (congrFun hL 1) 2
    change ψ (.inl 0) * conj (ψ (.inl 1)) + 0 = 0 at h
    simpa only [add_zero] using h
  have h2 : ψ (.inl 2) = 0 := by
    apply hzero
    have h := congrFun (congrFun hR 1) 2
    change ψ (.inl 0) * conj (ψ (.inl 2)) + 0 = 0 at h
    simpa only [add_zero] using h
  have hvac : ψ (.inr false) * conj (ψ (.inr false)) = L false false := by
    have h := congrFun (congrFun hL 0) 0
    change ψ (.inr false) * conj (ψ (.inr false)) +
      ψ (.inl 2) * conj (ψ (.inl 2)) = L false false at h
    simpa [h2] using h
  have hpair : ψ (.inr true) * conj (ψ (.inr true)) = L true true := by
    have h := congrFun (congrFun hL 2) 2
    change ψ (.inl 1) * conj (ψ (.inl 1)) +
      ψ (.inr true) * conj (ψ (.inr true)) = L true true at h
    simpa [h1] using h
  have hu : ψ (.inl 0) * conj (ψ (.inr false)) = u := by
    have h := congrFun (congrFun hL 1) 0
    change ψ (.inl 0) * conj (ψ (.inr false)) + 0 = u at h
    simpa only [add_zero] using h
  have hu' : ψ (.inr false) * conj (ψ (.inl 0)) = conj u := by
    simpa [mul_comm] using congrArg (conj : ℂ → ℂ) hu
  have qb : RationalEntry (b : ℂ) := by
    have he : L.trace + (b : ℂ) = 1 :=
      ((pure_coherent_iff b L R u 0 0 z hb.ne').1.mp
        ⟨rankOneDensity ψ, ⟨ψ, rfl⟩, ht, hL, hR, hz⟩).1
    rw [show (b : ℂ) = 1 - L.trace by linear_combination he]
    exact rationalComplex.sub_mem rationalComplex.one_mem
      (rationalComplex.sum_mem fun i _ => qL i i)
  let ρ := rankOneDensity (vacuumMiddle ψ) + rankOneDensity (doubleEndpoint ψ)
  refine ⟨ρ, (Matrix.posSemidef_vecMulVec_self_star _).add
      (Matrix.posSemidef_vecMulVec_self_star _), ?_, rank_two_outer _ _, ?_⟩
  · refine ⟨?_, ?_, ?_, by simp [ρ, vacuumMiddle, doubleEndpoint, rankOneDensity,
      Matrix.vecMulVec_apply, Pi.star_apply]⟩
    · have hdiag (i : Word) : ρ i i = rankOneDensity ψ i i := by
        rcases i with (i | i)
        · fin_cases i <;> simp [ρ, vacuumMiddle, doubleEndpoint, rankOneDensity,
            Matrix.vecMulVec_apply, Pi.star_apply, h1, h2]
        · cases i <;> simp [ρ, vacuumMiddle, doubleEndpoint, rankOneDensity,
            Matrix.vecMulVec_apply, Pi.star_apply]
      simpa only [Matrix.trace, Matrix.diag, hdiag] using ht
    · rw [← hL]
      ext i j : 1
      fin_cases i <;> fin_cases j <;> simp [edgeTrace, ρ, vacuumMiddle, doubleEndpoint,
        rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply, h1, h2]
      all_goals
        first
        | exact Or.inl rfl
        | change ψ (.inr false) * conj (ψ (.inr false)) + 0 * conj 0 =
            ψ (.inr false) * conj (ψ (.inr false))
          simp
        | change 0 * conj 0 + ψ (.inr true) * conj (ψ (.inr true)) =
            ψ (.inr true) * conj (ψ (.inr true))
          simp
    · rw [← hR]
      ext i j : 1
      fin_cases i <;> fin_cases j <;> simp [edgeTrace, ρ, vacuumMiddle, doubleEndpoint,
        rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply, h1, h2]
      all_goals
        first
        | exact Or.inl rfl
        | change ψ (.inr false) * conj (ψ (.inr false)) + 0 * conj 0 =
            ψ (.inr false) * conj (ψ (.inr false))
          simp
        | change 0 * conj 0 + ψ (.inr true) * conj (ψ (.inr true)) =
            ψ (.inr true) * conj (ψ (.inr true))
          simp
  · intro i j
    rcases i with (i | i) <;> rcases j with (j | j)
    · fin_cases i <;> fin_cases j <;> simp [ρ, vacuumMiddle, doubleEndpoint,
        rankOneDensity, Matrix.vecMulVec_apply, Pi.star_apply, hmid] <;>
        first | exact qb | exact rationalComplex.zero_mem
    · fin_cases i <;> cases j <;> simp [ρ, vacuumMiddle, doubleEndpoint, rankOneDensity,
        Matrix.vecMulVec_apply, Pi.star_apply, hu] <;> first | exact qu | exact rationalComplex.zero_mem
    · cases i <;> fin_cases j <;> simp [ρ, vacuumMiddle, doubleEndpoint, rankOneDensity,
        Matrix.vecMulVec_apply, Pi.star_apply, hu'] <;>
        first | exact (rationalConjugate ⟨u, qu⟩).property | exact rationalComplex.zero_mem
    · cases i <;> cases j <;> simp [ρ, vacuumMiddle, doubleEndpoint, rankOneDensity,
        Matrix.vecMulVec_apply, Pi.star_apply, hvac, hpair] <;>
        first | exact qL _ _ | exact rationalComplex.zero_mem

/-- A rational pair of edge marginals at positive middle occupation admits a rational
extension of rank at most two whenever it admits an ordinary pure extension. -/
theorem positive_rational_rank_le_two_of_pure
    (b : ℝ) (u v w : ℂ) (L R : Matrix Bool Bool ℂ)
    (hb : 0 < b)
    (qL : ∀ i j, RationalEntry (L i j)) (qR : ∀ i j, RationalEntry (R i j))
    (qu : RationalEntry u) (qv : RationalEntry v) (qw : RationalEntry w)
    (hPure : ∃ (z : ℂ) (ψ : Word → ℂ), MatchesCoherentData b L R u v w z (rankOneDensity ψ)) :
    ∃ (z : ℂ) (ρ : Matrix Word Word ℂ),
      ρ.PosSemidef ∧ MatchesCoherentData b L R u v w z ρ ∧
      ρ.rank ≤ 2 ∧ ∀ i j, RationalEntry (ρ i j) := by
  by_cases h : v = 0 ∧ w = 0
  · obtain ⟨rfl, rfl⟩ := h
    obtain ⟨z, ψ, hψ⟩ := hPure
    obtain ⟨ρ, hp, hd, hr, hq⟩ := separate_double_endpoint b u z L R hb qL qu ψ hψ
    exact ⟨0, ρ, hp, hd, hr, hq⟩
  · have hn : v ≠ 0 ∨ w ≠ 0 := by tauto
    obtain ⟨z, ψ, hd, hq⟩ := (positive_rational_purity_iff b u v w L R hb qL qR qu qv qw hPure).mpr
      (hn.elim Or.inl (fun h => Or.inr (Or.inl h)))
    exact ⟨z, rankOneDensity ψ, Matrix.posSemidef_vecMulVec_self_star ψ, hd,
      (Matrix.rank_vecMulVec_le ψ (star ψ)).trans (by decide), hq⟩

end D5.S3.Quantum.Entanglement.Marginals.FibPositiveRationalRank
