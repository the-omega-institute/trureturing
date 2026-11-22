/- GID: D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint.mixedUnitaryRank_seventy_three; instance=D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedActualSeedBounds.existsUnique_zero_closedBall; result=D5/S3/Quantum/QuantumChannels/WernerHolevo/ChirpedBasisEndpoint.mixedUnitaryRank_seventy_three
   digest: An exact order-73 zero yields a full symmetric unitary basis and mixed-unitary rank 2701. -/

import D5.S3.Quantum.QuantumChannels.WernerHolevo.ChirpedActualSeedBounds
import D5.S3.Quantum.QuantumChannels.WernerHolevo.TransversalNineGluing

/-! The recorded chirped systems give full symmetric unitary bases at any exact zero.
The chirped construction uses Ma's Theorem 5 and Proposition 12
(doi:10.5281/zenodo.24246318). The exact layout and row data come from the two replay inputs. -/

open scoped BigOperators ComplexConjugate
open ChirpedAnalyticDrift
open ChirpedAnalyticDrift.ReplayBridge (pullback ValidSeed replayRows)
open D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open AffineNineRank (HasMixedUnitaryDecomposition)

namespace ChirpedBasisEndpoint

noncomputable section

section Fourier

variable {n m : ℕ} [NeZero n]

private abbrev half (n : ℕ) : ZMod n := (((n + 1) / 2 : ℕ) : ZMod n)

def chirp : ChirpedFinite.Seed → ℕ
  | .chirped c => c.phase
  | .constantSpectrum _ => 0

private theorem pullback_chirp (s : ChirpedFinite.Seed) :
    (pullback (n := n) (m := m) s).chirp = (chirp s : ZMod n) * half n := by
  cases s <;> simp [pullback, chirp, Nat.cast_mul, mul_comm]

def shift (u : (ZMod n)ˣ) (p : ℕ) (f : ZMod n → ℂ) : ZMod n → ℂ :=
  fun d => f ((u ^ p).mulLeft d)

theorem shift_zero (u : (ZMod n)ˣ) (f : ZMod n → ℂ) : shift u 0 f = f := by
  funext d
  change f ((↑(u ^ 0) : ZMod n) * d) = f d
  simp

private theorem shift_add (u : (ZMod n)ˣ) (a b : ℕ) (f : ZMod n → ℂ) :
    shift u (a + b) f = shift u a (shift u b f) := by
  funext d
  change f ((↑(u ^ (a + b)) : ZMod n) * d) = f (↑(u ^ b) * (↑(u ^ a) * d))
  rw [pow_add, Units.val_mul]
  congr 1
  ac_rfl

theorem shift_mod (u : (ZMod n)ˣ) (L : ℕ) (f : ZMod n → ℂ)
    (h : shift u L f = f) (p : ℕ) : shift u p f = shift u (p % L) f := by
  have hmul : ∀ k, shift u (L * k) f = f := by
    intro k
    induction k with
    | zero => simp only [mul_zero, shift_zero]
    | succ k ih => rw [Nat.mul_succ, shift_add, h, ih]
  calc
    shift u p f = shift u (p % L + L * (p / L)) f :=
      congrArg (fun k => shift u k f) (Nat.mod_add_div p L).symm
    _ = shift u (p % L) f := by rw [shift_add, hmul]

private def shiftedSpectrum (u : (ZMod n)ˣ) (μ : ZMod n → ℂ) : ZMod n → ℂ :=
  fun l => μ (u.mulLeft.symm l)

private theorem kernel_mul (u : (ZMod n)ˣ) (μ : ZMod n → ℂ) (d : ZMod n) :
    ChirpedCirculantGram.kernel μ (u.mulLeft d) =
      ChirpedCirculantGram.kernel (shiftedSpectrum u μ) d := by
  have hsum : (∑ l, ZMod.stdAddChar (l * u.mulLeft d) * μ l) =
      ∑ l, ZMod.stdAddChar (l * d) * shiftedSpectrum u μ l := by
    refine Fintype.sum_equiv u.mulLeft
      (fun l => ZMod.stdAddChar (l * u.mulLeft d) * μ l)
      (fun l => ZMod.stdAddChar (l * d) * shiftedSpectrum u μ l) ?_
    intro l
    have harg : l * u.mulLeft d = u.mulLeft l * d := by
      change l * ((u : ZMod n) * d) = ((u : ZMod n) * l) * d
      ac_rfl
    simp only [shiftedSpectrum, Equiv.symm_apply_apply, harg]
  exact congrArg (fun z : ℂ => (n : ℂ)⁻¹ * z) hsum

private theorem shiftedSpectrum_even (u : (ZMod n)ˣ) {μ : ZMod n → ℂ}
    (hμ : ∀ l, μ (-l) = μ l) (l : ZMod n) :
    shiftedSpectrum u μ (-l) = shiftedSpectrum u μ l := by
  change μ ((↑(u⁻¹) : ZMod n) * -l) = μ ((↑(u⁻¹) : ZMod n) * l)
  rw [mul_neg, hμ]

private abbrev baseSpectrum (sign : Fin m → ℤ) (s : ChirpedFinite.Seed) (x : Fin m → ℝ) :=
  ChirpedAnalyticDrift.spectrum sign (pullback (n := n) s) x

abbrev baseSeed (sign : Fin m → ℤ) (s : ChirpedFinite.Seed) (x : Fin m → ℝ) :=
  seedValue sign (pullback (n := n) s) (Equiv.refl _) x

private theorem baseSpectrum_norm (sign : Fin m → ℤ) (hs : ∀ i, sign i = 1 ∨ sign i = -1)
    (s : ChirpedFinite.Seed) (x : Fin m → ℝ) (l : ZMod n) :
    ‖baseSpectrum sign s x l‖ = 1 := by
  unfold baseSpectrum
  cases h : (pullback (n := n) (m := m) s).coord l with
  | none => simp [ChirpedAnalyticDrift.spectrum, h]
  | some i =>
    simpa only [ChirpedAnalyticDrift.spectrum, h] using
      (ChirpedReplay.cayley_norm_bounds (x i) (sign i) (hs i)).1

private theorem baseSpectrum_even (sign : Fin m → ℤ)
    (s : ChirpedFinite.Seed) (x : Fin m → ℝ)
    (h : ∀ l : ZMod n, (pullback (m := m) s).coord (-l) = (pullback (m := m) s).coord l)
    (l : ZMod n) : baseSpectrum sign s x (-l) = baseSpectrum sign s x l := by
  unfold baseSpectrum ChirpedAnalyticDrift.spectrum
  rw [h l]

def shiftedChirp (u : (ZMod n)ˣ) (p : ℕ) (s : ChirpedFinite.Seed) : ZMod n :=
  (chirp s : ZMod n) * (↑(u ^ p) : ZMod n) ^ 2

private theorem baseSeed_eq (sign : Fin m → ℤ) (s : ChirpedFinite.Seed) (x : Fin m → ℝ) :
    baseSeed (n := n) sign s x =
      ChirpedCirculantGram.seed (half n) (chirp s) (baseSpectrum sign s x) := by
  funext d
  unfold baseSeed seedValue transform ChirpedCirculantGram.seed
  rw [Equiv.refl_apply, pullback_chirp]

/-- Reindexing the DFT scales the chirp by the square of the column multiplier
and pulls back the spectrum by its inverse. -/
private theorem shifted_seed (u : (ZMod n)ˣ) (p : ℕ) (sign : Fin m → ℤ)
    (s : ChirpedFinite.Seed) (x : Fin m → ℝ) :
    shift u p (baseSeed sign s x) = ChirpedCirculantGram.seed (half n) (shiftedChirp u p s)
      (shiftedSpectrum (u ^ p) (baseSpectrum sign s x)) := by
  rw [baseSeed_eq]
  funext d
  unfold shift ChirpedCirculantGram.seed
  rw [kernel_mul]
  have he : (chirp s : ZMod n) * half n * ((u ^ p).mulLeft d) ^ 2 =
      shiftedChirp u p s * half n * d ^ 2 := by
    change (chirp s : ZMod n) * half n * ((↑(u ^ p) : ZMod n) * d) ^ 2 = _
    unfold shiftedChirp
    ring
  rw [he]

theorem seed_period (u : (ZMod n)ˣ) (L : ℕ) (sign : Fin m → ℤ)
    (s : ChirpedFinite.Seed) (x : Fin m → ℝ) (hc : shiftedChirp u L s = (chirp s : ZMod n))
    (hs : ∀ l : ZMod n, (pullback (m := m) s).coord ((u ^ L).mulLeft l) =
      (pullback (m := m) s).coord l) :
    shift u L (baseSeed sign s x) = baseSeed sign s x := by
  have hμ : shiftedSpectrum (u ^ L) (baseSpectrum sign s x) = baseSpectrum sign s x := by
    funext l
    have h := hs ((u ^ L).mulLeft.symm l)
    rw [Equiv.apply_symm_apply] at h
    change baseSpectrum sign s x ((u ^ L).mulLeft.symm l) = baseSpectrum sign s x l
    unfold baseSpectrum ChirpedAnalyticDrift.spectrum
    rw [← h]
  rw [shifted_seed, hc, hμ, baseSeed_eq]

end Fourier

section Correlations

variable {n m : ℕ} [NeZero n]

def gram (f g : ZMod n → ℂ) : ℂ := ∑ d, conj (f d) * g d

private theorem gram_shift (u : (ZMod n)ˣ) (t : ℕ) (f g : ZMod n → ℂ) :
    gram (shift u t f) (shift u t g) = gram f g :=
  Fintype.sum_equiv (u ^ t).mulLeft _ _ (fun _ => rfl)

private theorem gram_swap (f g : ZMod n → ℂ) : conj (gram f g) = gram g f := by
  simp only [gram, map_sum, map_mul, starRingEnd_self_apply]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- A shift that squares to the identity on the seed has real self-correlation. -/
private theorem midpoint_im_zero (u : (ZMod n)ˣ) (p : ℕ) (f : ZMod n → ℂ)
    (h : shift u (p + p) f = f) : (gram (shift u p f) f).im = 0 := by
  have hconj : conj (gram (shift u p f) f) = gram (shift u p f) f := by
    calc
      _ = gram f (shift u p f) := gram_swap _ _
      _ = gram (shift u p f) (shift u p (shift u p f)) := (gram_shift u p _ _).symm
      _ = gram (shift u p f) f := by rw [← shift_add, h]
  have him := congrArg Complex.im hconj
  rw [Complex.conj_im] at him
  linarith

def recordedGram (u : (ZMod n)ˣ) (v : ℕ → ZMod n → ℂ)
    (c : ChirpedFinite.Constraint) : ℂ :=
  gram (shift u c.power (v c.left)) (v c.right)

abbrev HasRow (pick : Fin m → ChirpedFinite.Constraint) (imag : Fin m → Bool)
    (c : ChirpedFinite.Constraint) (b : Bool) : Prop :=
  ∃ i, pick i = c ∧ imag i = b

theorem recorded_gram_zero (u : (ZMod n)ˣ) (sign : Fin m → ℤ)
    (data : ℕ → ChirpedFinite.Seed) (pick : Fin m → ChirpedFinite.Constraint)
    (imag : Fin m → Bool) (x : Fin m → ℝ) (c : ChirpedFinite.Constraint)
    (hF : residual sign (replayRows u pick imag data) x = 0)
    (hRe : HasRow pick imag c false)
    (hIm : HasRow pick imag c true ∨
      c.left = c.right ∧ shift u (c.power + c.power) (baseSeed sign (data c.left) x) =
        baseSeed sign (data c.left) x) :
    recordedGram u (fun a => baseSeed sign (data a) x) c = 0 := by
  let v := fun a => baseSeed (n := n) sign (data a) x
  have hrow (b : Bool) (h : HasRow pick imag c b) : projection b (recordedGram u v c) = 0 := by
    obtain ⟨i, hi, hb⟩ := h
    have hcoord := congrFun hF i
    change projection (imag i) (recordedGram u v (pick i)) = 0 at hcoord
    rw [hi, hb] at hcoord
    exact hcoord
  have hre : (recordedGram u v c).re = 0 := by
    simpa [projection_apply, ChirpedReplay.project] using hrow false hRe
  have him : (recordedGram u v c).im = 0 := by
    rcases hIm with him | ⟨he, hp⟩
    · simpa [projection_apply, ChirpedReplay.project] using hrow true him
    · unfold recordedGram
      rw [← he]
      exact midpoint_im_zero u c.power (v c.left) hp
  exact Complex.ext (hre.trans Complex.zero_re.symm) (him.trans Complex.zero_im.symm)

/-- A common shift of a recorded row is chosen using the longer of the two periods.
The residue checks below validate the choice against both periods. -/
private def commonShift (period : ℕ → ℕ) (c : ChirpedFinite.Constraint)
    (i j : ℕ × ℕ) : ℕ :=
  if period i.1 ≤ period j.1 then j.2 else i.2 + period i.1 - c.power % period i.1

private abbrev Covers (period : ℕ → ℕ) (c : ChirpedFinite.Constraint)
    (i j : ℕ × ℕ) : Prop :=
  c.left = i.1 ∧ c.right = j.1 ∧
    (c.power + commonShift period c i j) % period i.1 = i.2 ∧
    commonShift period c i j % period j.1 = j.2

def CoveredPair {b : ℕ} (period : ℕ → ℕ) (rows : Fin b → ChirpedFinite.Constraint)
    (i j : ℕ × ℕ) : Prop :=
  ∃ k, Covers period (rows k) i j ∨ Covers period (rows k) j i

private instance {b : ℕ} (period : ℕ → ℕ) (rows : Fin b → ChirpedFinite.Constraint)
    (i j : ℕ × ℕ) : Decidable (CoveredPair period rows i j) := by
  unfold CoveredPair
  exact Fintype.decidableExistsFintype

theorem gram_zero_of_coverage {κ : Type*} (u : (ZMod n)ˣ) (period : ℕ → ℕ)
    (v : ℕ → ZMod n → ℂ) (orbit : κ → ℕ × ℕ)
    (rows : ℕ → ChirpedFinite.Constraint)
    (b : ℕ) (hperiod : ∀ i, shift u (period (orbit i).1) (v (orbit i).1) = v (orbit i).1)
    (hrows : ∀ k : Fin b, recordedGram u v (rows k.val) = 0)
    (hcover : ∀ i j, i ≠ j →
      CoveredPair period (fun k : Fin b => rows k.val) (orbit i) (orbit j))
    {i j : κ} (hij : i ≠ j) :
    gram (shift u (orbit i).2 (v (orbit i).1)) (shift u (orbit j).2 (v (orbit j).1)) = 0 := by
  have hforward (i j : κ) (k : Fin b) (hc : Covers period (rows k.val) (orbit i) (orbit j)) :
      gram (shift u (orbit i).2 (v (orbit i).1)) (shift u (orbit j).2 (v (orbit j).1)) = 0 := by
    let c := rows k.val
    let t := commonShift period c (orbit i) (orbit j)
    obtain ⟨hl, hr, hpl, hpr⟩ := hc
    change c.left = (orbit i).1 at hl
    change c.right = (orbit j).1 at hr
    change (c.power + t) % period (orbit i).1 = (orbit i).2 at hpl
    change t % period (orbit j).1 = (orbit j).2 at hpr
    have hleft : shift u t (shift u c.power (v c.left)) = shift u (orbit i).2 (v (orbit i).1) := by
      rw [← shift_add, hl, shift_mod u _ _ (hperiod i), add_comm t c.power, hpl]
    have hright : shift u t (v c.right) = shift u (orbit j).2 (v (orbit j).1) := by
      rw [hr, shift_mod u _ _ (hperiod j), hpr]
    rw [← hleft, ← hright, gram_shift]
    exact hrows k
  have h := hcover i j hij
  unfold CoveredPair at h
  obtain ⟨k, hk | hk⟩ := h
  · exact hforward i j k hk
  · rw [← gram_swap, hforward j i k hk, map_zero]

end Correlations

section Basis

variable {n m : ℕ} [NeZero n] {ι : Type*} [Fintype ι]

private def family (u : (ZMod n)ˣ) (sign : Fin m → ℤ) (data : ℕ → ChirpedFinite.Seed)
    (orbit : ι → ℕ × ℕ) (x : Fin m → ℝ) (i : ι × ZMod n) :
    Matrix (ZMod n) (ZMod n) ℂ :=
  let a := (orbit i.1).1
  let p := (orbit i.1).2
  ChirpedCirculantGram.chirped (shiftedChirp u p (data a)) i.2
    (shiftedSpectrum (u ^ p) (baseSpectrum sign (data a) x))

/-- The full family is assembled from distinct shifted seeds and all modulations.
The dimension count promotes Hilbert–Schmidt orthogonality to a spanning basis. -/
def assemble [Nonempty ι] (u : (ZMod n)ˣ) (sign : Fin m → ℤ)
    (data : ℕ → ChirpedFinite.Seed)
    (orbit : ι → ℕ × ℕ) (x : Fin m → ℝ) (hh : 2 * half n = 1)
    (hsign : ∀ j, sign j = 1 ∨ sign j = -1)
    (heven : ∀ i l, (pullback (n := n) (m := m) (data (orbit i).1)).coord (-l) =
      (pullback (n := n) (m := m) (data (orbit i).1)).coord l)
    (hgram : ∀ i j, i ≠ j →
      gram (shift u (orbit i).2 (baseSeed sign (data (orbit i).1) x))
        (shift u (orbit j).2 (baseSeed sign (data (orbit j).1) x)) = 0)
    (hcard : Fintype.card (ι × ZMod n) = (n + 1).choose 2) :
    TransversalNine.UnitaryBasis (ι × ZMod n) (ZMod n) := by
  classical
  let c (i : ι) := shiftedChirp u (orbit i).2 (data (orbit i).1)
  let μ (i : ι) := shiftedSpectrum (u ^ (orbit i).2) (baseSpectrum sign (data (orbit i).1) x)
  let A := family u sign data orbit x
  have hA (i : ι) (v : ZMod n) : A (i, v) = ChirpedCirculantGram.chirped (c i) v (μ i) := rfl
  have hnorm (i : ι) (l : ZMod n) : ‖μ i l‖ = 1 := baseSpectrum_norm sign hsign _ _ _
  have hunit (i : ι × ZMod n) : A i ∈ Matrix.unitaryGroup (ZMod n) ℂ := by
    rcases i with ⟨i, v⟩
    rw [hA]
    exact ChirpedCirculantGram.chirped_unitary _ _ _ (hnorm i)
  have hsym (i : ι × ZMod n) : (A i).IsSymm := by
    rcases i with ⟨i, v⟩
    rw [hA]
    exact ChirpedCirculantGram.chirped_transpose _ _ _
      (shiftedSpectrum_even _ (baseSpectrum_even sign _ x (heven i)))
  have hseed (i : ι) : ChirpedCirculantGram.seed (half n) (c i) (μ i) =
      shift u (orbit i).2 (baseSeed sign (data (orbit i).1) x) :=
    (shifted_seed u (orbit i).2 sign _ x).symm
  have horth (i j : ι × ZMod n) (hij : i ≠ j) : AffineNine.hs (A i) (A j) = 0 := by
    rcases i with ⟨i, v⟩
    rcases j with ⟨j, w⟩
    have hsum (M N : Matrix (ZMod n) (ZMod n) ℂ) :
        AffineNineRank.hsInner M N = AffineNine.hs M N :=
      AffineNineRank.hsInner_eq_sum M N
    rw [← hsum, hA i v, hA j w, AffineNineRank.hsInner_eq_sum]
    rw [← Fintype.sum_prod_type (fun xy : ZMod n × ZMod n =>
      star (ChirpedCirculantGram.chirped (c i) v (μ i) xy.1 xy.2) *
        ChirpedCirculantGram.chirped (c j) w (μ j) xy.1 xy.2)]
    by_cases he : i = j
    · subst j
      rw [ChirpedCirculantGram.chirped_gram_same_seed _ hh _ _ _ _ (hnorm i)]
      exact if_neg (fun hvw => hij (Prod.ext rfl hvw))
    · rw [ChirpedCirculantGram.chirped_gram _ hh]
      change gram (ChirpedCirculantGram.seed (half n) (c i) (μ i))
        (ChirpedCirculantGram.seed (half n) (c j) (μ j)) * _ = 0
      rw [hseed i, hseed j, hgram i j he, zero_mul]
  have hli : LinearIndependent ℂ A := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    let pairing : Matrix (ZMod n) (ZMod n) ℂ →ₗ[ℂ] ℂ :=
      { toFun := AffineNine.hs (A i)
        map_add' M N := by simp [AffineNine.hs, mul_add, Finset.sum_add_distrib]
        map_smul' z M := by simp [AffineNine.hs, Finset.mul_sum, mul_left_comm] }
    have h := congrArg pairing ha
    simp only [map_sum, map_smul, map_zero] at h
    change (∑ j, a j * AffineNine.hs (A i) (A j)) = 0 at h
    rw [Finset.sum_eq_single i] at h
    · rw [AffineNine.hs_self_of_unitary (hunit i)] at h
      exact (mul_eq_zero.mp h).resolve_right (Nat.cast_ne_zero.mpr (by
        rw [ZMod.card]
        exact NeZero.ne n))
    · intro j _ hji
      rw [horth i j hji.symm, mul_zero]
    · simp
  let b : ι × ZMod n → AffineNine.symmetric (ZMod n) := fun i => ⟨A i, hsym i⟩
  let B := basisOfLinearIndependentOfCardEqFinrank (b := b)
    (LinearIndependent.of_comp (AffineNine.symmetric (ZMod n)).subtype hli)
    (hcard.trans (by rw [AffineNine.finrank_symmetric, ZMod.card]))
  have hB (i : ι × ZMod n) : (B i : Matrix (ZMod n) (ZMod n) ℂ) = A i := by
    dsimp only [B]
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact ⟨B, fun i => hB i ▸ hunit i, fun i j hij => by rw [hB, hB]; exact horth i j hij⟩

theorem hasBasis_of_family
    (hcard : Fintype.card (ι × ZMod n) = (n + 1).choose 2)
    (B : TransversalNine.UnitaryBasis (ι × ZMod n) (ZMod n)) : TransversalNine.HasBasis n :=
  ⟨B.reindex (Fintype.equivFinOfCardEq hcard) (Fintype.equivFinOfCardEq (ZMod.card n)).symm⟩

end Basis

namespace Order73

open Chirped73

local instance : NeZero n := ⟨by decide⟩

/-- Inverse of the actual multiplier 5 from the replay input. -/
private def inverseUnit : (ZMod n)ˣ :=
  ⟨(inverseMultiplier : ZMod n), (multiplier : ZMod n), by decide, by decide⟩

private def period : ℕ → ℕ
  | 0 => 36
  | _ => 1

private def orbit (i : Fin 37) : ℕ × ℕ :=
  if i.val < 36 then (0, i.val) else (1, 0)

private theorem orbit_domain : ∀ i : Fin 37, (orbit i).1 < seeds.length := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem valid : ∀ a : Fin seeds.length, ValidSeed n m (seed a.val) := by
  exact fun a => Chirped73.valid_seed a.val a.isLt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem evenCoord : ∀ a : Fin seeds.length, ∀ l : ZMod n,
    (pullback (m := m) (seed a.val)).coord (-l) = (pullback (m := m) (seed a.val)).coord l := by
  intro a
  fin_cases a <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem stabilizers : ∀ a : Fin seeds.length,
    shiftedChirp inverseUnit (period a.val) (seed a.val) = (chirp (seed a.val) : ZMod n) ∧
    ∀ l : ZMod n,
      (pullback (m := m) (seed a.val)).coord ((inverseUnit ^ period a.val).mulLeft l) =
      (pullback (m := m) (seed a.val)).coord l := by
  intro a
  fin_cases a <;> decide +kernel

private abbrev signs (i : Fin m) : ℤ := signEntry i.val

private theorem periodic (x : Fin m → ℝ) (a : ℕ) (ha : a < seeds.length) :
    shift inverseUnit (period a) (baseSeed signs (seed a) x) = baseSeed signs (seed a) x :=
  let h := stabilizers ⟨a, ha⟩
  seed_period inverseUnit (period a) signs (seed a) x h.1 h.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
/-- The row lacking an imaginary projection is the orbit midpoint.
The check uses the replay's actual row indices and recorded constraints. -/
private theorem projections : ∀ k : Fin constraints.length,
    let c := constraint k.val
    HasRow pick imag c false ∧ (HasRow pick imag c true ∨
      c.includeImag = false ∧ c.left = c.right ∧
        (c.power + c.power) % period c.left = 0) := by
  intro k
  fin_cases k <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
private theorem coverage : ∀ i j : Fin 37, i < j →
    CoveredPair period (fun k : Fin constraints.length => constraint k.val)
      (orbit i) (orbit j) := by
  intro i
  fin_cases i <;> decide +kernel

private theorem residual_at_zero (x : Fin m → ℝ) (hx : F x = 0) :
    residual signs (replayRows inverseUnit pick imag seed) x = 0 := by
  have hDomain (i : Fin m) :=
    constraints_domain ⟨(equation i.val).1, equation_domain i⟩
  have h := ChirpedAnalyticDrift.ReplayBridge.residual_eq signs inverseUnit inverseMultiplier
    rfl pick imag seed
    (fun i => valid ⟨(pick i).left, (hDomain i).1⟩)
    (fun i => valid ⟨(pick i).right, (hDomain i).2⟩) x
  exact h.trans hx

private theorem recorded_rows_zero (x : Fin m → ℝ) (hx : F x = 0)
    (k : Fin constraints.length) :
    recordedGram inverseUnit (fun a => baseSeed signs (seed a) x) (constraint k.val) = 0 := by
  have h := projections k
  apply recorded_gram_zero inverseUnit signs seed pick imag x (constraint k.val)
    (residual_at_zero x hx) h.1
  rcases h.2 with hi | ⟨_, he, hp⟩
  · exact Or.inl hi
  · refine Or.inr ⟨he, ?_⟩
    rw [shift_mod inverseUnit _ _ (periodic x _ (constraints_domain k).1), hp, shift_zero]

private theorem seed_orthogonal (x : Fin m → ℝ) (hx : F x = 0) (i j : Fin 37) (hij : i ≠ j) :
    gram (shift inverseUnit (orbit i).2 (baseSeed signs (seed (orbit i).1) x))
      (shift inverseUnit (orbit j).2 (baseSeed signs (seed (orbit j).1) x)) = 0 := by
  refine gram_zero_of_coverage inverseUnit period (fun a => baseSeed signs (seed a) x)
    orbit constraint constraints.length (fun i => periodic x _ (orbit_domain i))
    (recorded_rows_zero x hx) ?_ hij
  intro a b hab
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact coverage a b hab
  · have h := coverage b a hba
    unfold CoveredPair at h ⊢
    obtain ⟨k, hk⟩ := h
    exact ⟨k, hk.symm⟩

private theorem family_card : Fintype.card (Fin 37 × ZMod n) = (n + 1).choose 2 := by
  rw [Fintype.card_prod, Fintype.card_fin, ZMod.card] <;> decide

/-- The 37 shifted seeds and their 73 modulations give all 2701 basis matrices. -/
def unitaryBasis (x : Fin m → ℝ) (hx : F x = 0) :
    TransversalNine.UnitaryBasis (Fin 37 × ZMod n) (ZMod n) :=
  assemble inverseUnit signs seed orbit x (by decide) (fun i => (signs_unit i).symm)
    (fun i => evenCoord ⟨(orbit i).1, orbit_domain i⟩)
    (seed_orthogonal x hx) family_card

theorem hasBasis_of_zero (x : Fin m → ℝ) (hx : F x = 0) : TransversalNine.HasBasis 73 :=
  hasBasis_of_family family_card (unitaryBasis x hx)

/-- The order-73 symmetric Werner–Holevo channel has mixed-unitary rank 2701. -/
theorem mixedUnitaryRank_seventy_three :
    ∃ channel : QuantumChannel (Fin 73) (Fin 73),
      (∀ X : Matrix (Fin 73) (Fin 73) ℂ, CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        AffineNineRank.symmetricWernerHolevo (Fin 73) X) ∧
      IsLeast {k : ℕ | HasMixedUnitaryDecomposition channel k} 2701 := by
  obtain ⟨x, hx, _⟩ := Chirped73.existsUnique_zero_closedBall
  exact TransversalNine.rank_exact (hasBasis_of_zero x hx.2)

end Order73


end
end ChirpedBasisEndpoint
