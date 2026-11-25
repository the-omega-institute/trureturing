/- GID: D5/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/RankTwoHiddenProcess
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rank-two unital channels can hide correlations from every proper output. -/

import D5.S3.Quantum.ProcessReconstruction.ParityFamily
import D5.S3.Quantum.ProcessReconstruction.SwapReconstruction

/-! Rank-two channels with identical proper output maps and maximal diamond distance. -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Entanglement.LocalObservationPartialTraceEquivalence

namespace UnitaryReconstruction.RankTwoHiddenProcess

universe u

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The block containing the two distinguished basis words is indexed by `true`. -/
def inBlock (u v x : a) : Bool := decide (x = u ∨ x = v)

def phase (v : a) (flip : Bool) (x : a) : ℂ :=
  if flip = true ∧ x = v then -1 else 1

omit [Fintype a] in
private theorem phase_star (v : a) (flip : Bool) (x : a) :
    star (phase v flip x) = phase v flip x := by
  by_cases h : flip = true ∧ x = v <;> simp [phase, h]

omit [Fintype a] in
private theorem phase_mul_self (v : a) (flip : Bool) (x : a) :
    phase v flip x * phase v flip x = 1 := by
  by_cases h : flip = true ∧ x = v <;> simp [phase, h]

def reflection (u v x : a) : ℂ := if inBlock u v x then 1 else -1

omit [Fintype a] in
private theorem reflection_star (u v x : a) : star (reflection u v x) = reflection u v x := by
  cases h : inBlock u v x <;> simp [reflection, h]

omit [Fintype a] in
private theorem reflection_mul_self (u v x : a) :
    reflection u v x * reflection u v x = 1 := by
  cases h : inBlock u v x <;> simp [reflection, h]

/-- The Kraus operators are `P,Q` for `flip = false` and `DP,Q` for `flip = true`. -/
def kraus (u v : a) (flip block : Bool) : Matrix a a ℂ :=
  diagonal (fun x => if inBlock u v x = block then phase v flip x else 0)

private theorem kraus_complete (u v : a) (flip : Bool) :
    (∑ b, (kraus u v flip b)ᴴ * kraus u v flip b) = 1 := by
  rw [Fintype.sum_bool]
  ext x y
  by_cases hxy : x = y
  · subst y
    cases hx : inBlock u v x <;>
      simp [kraus, hx, apply_ite, phase_star, phase_mul_self]
  · simp [kraus, Matrix.diagonal_apply_ne _ hxy, Matrix.one_apply_ne hxy]

/-- The canonical CPTP channel induced by the displayed two Kraus operators. -/
def hiddenChannel (u v : a) (flip : Bool) : QuantumChannel a a :=
  (finite_kraus_quantum_channel (kraus u v flip) (kraus_complete u v flip)).choose

theorem hiddenChannel_kraus (u v : a) (flip : Bool) (X : Matrix a a ℂ) :
    CStarMatrix.ofMatrix.symm ((hiddenChannel u v flip).toCompletelyPositiveMap
      (CStarMatrix.ofMatrix X)) = ∑ b, kraus u v flip b * X * (kraus u v flip b)ᴴ :=
  (finite_kraus_quantum_channel (kraus u v flip) (kraus_complete u v flip)).choose_spec X

theorem hiddenChannel_entry (u v : a) (flip : Bool) (X : Matrix a a ℂ) (x y : a) :
    (hiddenChannel u v flip).toCompletelyPositiveMap (CStarMatrix.ofMatrix X) x y =
      if inBlock u v x = inBlock u v y then phase v flip x * X x y * phase v flip y
      else 0 := by
  change CStarMatrix.ofMatrix.symm
    ((hiddenChannel u v flip).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) x y = _
  rw [hiddenChannel_kraus, Fintype.sum_bool]
  cases hx : inBlock u v x <;> cases hy : inBlock u v y <;>
    simp [kraus, Matrix.diagonal_mul, Matrix.mul_diagonal, hx, hy, phase_star]

theorem hiddenChannel_unital (u v : a) (flip : Bool) :
    (hiddenChannel u v flip).toCompletelyPositiveMap 1 = 1 := by
  ext x y
  change (hiddenChannel u v flip).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (1 : Matrix a a ℂ)) x y = (1 : Matrix a a ℂ) x y
  rw [hiddenChannel_entry]
  by_cases h : x = y
  · subst y
    simp [phase_mul_self]
  · simp [Matrix.one_apply_ne h]

/-- The diagonal unitaries are `D^flip` and `D^flip (P - Q)`. -/
def mixingUnitary (u v : a) (flip reflect : Bool) : unitaryGroup a ℂ := by
  let w : a → ℂ := fun x => phase v flip x * if reflect then reflection u v x else 1
  refine ⟨diagonal w, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  change diagonal w * (diagonal w)ᴴ = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext x y
  by_cases h : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply,
      w, star_mul, phase_star]
    cases reflect
    · simp [phase_mul_self]
    · simp only [↓reduceIte, reflection_star]
      calc
        _ = (phase v flip x * phase v flip x) * (reflection u v x * reflection u v x) := by ring
        _ = 1 := by simp [phase_mul_self, reflection_mul_self]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

theorem hiddenChannel_randomUnitary (u v : a) (flip : Bool) (X : CStarMatrix a a ℂ) :
    (hiddenChannel u v flip).toCompletelyPositiveMap X =
      (1 / 2 : ℂ) •
        ((conjugation (mixingUnitary u v flip false)).toCompletelyPositiveMap X +
         (conjugation (mixingUnitary u v flip true)).toCompletelyPositiveMap X) := by
  let Y := CStarMatrix.ofMatrix.symm X
  have h (b : Bool) (x y : a) :
      (conjugation (mixingUnitary u v flip b)).toCompletelyPositiveMap X x y =
        (phase v flip x * if b then reflection u v x else 1) *
          Y x y * (phase v flip y * if b then reflection u v y else 1) := by
    have he := congrArg (fun M : Matrix a a ℂ => M x y)
      (conjugation_apply (mixingUnitary u v flip b) Y)
    let w : a → ℂ := fun x => phase v flip x * if b then reflection u v x else 1
    change (conjugation (mixingUnitary u v flip b)).toCompletelyPositiveMap X x y =
      (diagonal w * Y * (diagonal w)ᴴ) x y at he
    rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have hw (i : a) : star (w i) = w i := by
      cases b <;> simp [w, star_mul, phase_star, reflection_star,
        mul_comm (reflection u v i) (phase v flip i)]
    simpa only [Matrix.of_apply, Pi.star_apply, hw] using he
  ext x y
  change (hiddenChannel u v flip).toCompletelyPositiveMap (CStarMatrix.ofMatrix Y) x y =
    (1 / 2 : ℂ) * ((conjugation (mixingUnitary u v flip false)).toCompletelyPositiveMap X x y +
      (conjugation (mixingUnitary u v flip true)).toCompletelyPositiveMap X x y)
  rw [hiddenChannel_entry, h, h]
  cases hx : inBlock u v x <;> cases hy : inBlock u v y <;>
    simp [reflection, hx, hy] <;> ring

/-- Only the two opposite off-diagonal entries in the distinguished block can change. -/
theorem hiddenChannel_entry_eq (u v : a) (X : Matrix a a ℂ) (x y : a)
    (hxy : ¬ (x = u ∧ y = v)) (hyx : ¬ (x = v ∧ y = u)) :
    (hiddenChannel u v false).toCompletelyPositiveMap (CStarMatrix.ofMatrix X) x y =
      (hiddenChannel u v true).toCompletelyPositiveMap (CStarMatrix.ofMatrix X) x y := by
  rw [hiddenChannel_entry, hiddenChannel_entry]
  by_cases hx : x = v <;> by_cases hy : y = v
  · simp [phase, hx, hy]
  · have hyu : y ≠ u := fun h => hyx ⟨hx, h⟩
    simp [inBlock, hx, hy, hyu]
  · have hxu : x ≠ u := fun h => hxy ⟨h, hy⟩
    simp [inBlock, hx, hy, hxu]
  · simp [phase, hx, hy]

open ParityFamily (Bits Kept Discarded split)

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def zeroWord : Bits ι := fun _ => false
def oneWord : Bits ι := fun _ => true

def channel (flip : Bool) : QuantumChannel (Bits ι) (Bits ι) :=
  hiddenChannel zeroWord oneWord flip

omit [Fintype ι] in
private theorem discarded_words_ne (s : Finset ι) (k : ι) (hk : k ∉ s) :
    ((split s) (zeroWord : Bits ι)).1 ≠ ((split s) (oneWord : Bits ι)).1 := by
  intro h
  have hk' := congrFun h (⟨k, hk⟩ : {j // j ∉ s})
  change false = true at hk'
  cases hk'

/-- Equality of the actual reduced CPTP maps on the full input for every proper output. -/
theorem proper_output_eq (s : Finset ι) (hs : s ≠ Finset.univ) :
    (discard (split s)).comp (channel false) = (discard (split s)).comp (channel true) := by
  obtain ⟨k, hk⟩ : ∃ k, k ∉ s := by
    by_contra! h
    exact hs (Finset.eq_univ_iff_forall.mpr h)
  have hwords := discarded_words_ne s k hk
  apply channel_ext
  intro X
  simp only [QuantumChannel.comp_apply]
  apply CStarMatrix.ofMatrix.symm.injective
  have happly (flip : Bool) :
      CStarMatrix.ofMatrix.symm ((discard (split s)).toCompletelyPositiveMap
        ((channel flip).toCompletelyPositiveMap X)) =
      partialTraceFirst ((CStarMatrix.ofMatrix.symm
        ((channel flip).toCompletelyPositiveMap X)).submatrix (split s).symm (split s).symm) := by
    rw [← discard_apply, Equiv.apply_symm_apply]
  rw [happly, happly]
  ext x y
  simp only [partialTraceFirst, Matrix.submatrix_apply]
  apply Finset.sum_congr rfl
  intro z _
  let p := (split s).symm (z, x)
  let q := (split s).symm (z, y)
  have hfirst : ((split s) p).1 = ((split s) q).1 := by simp [p, q]
  change (channel false).toCompletelyPositiveMap X p q =
    (channel true).toCompletelyPositiveMap X p q
  rw [← CStarMatrix.ofMatrix.apply_symm_apply X]
  exact hiddenChannel_entry_eq zeroWord oneWord _ p q
    (fun ⟨hp, hq⟩ => hwords (hp ▸ hq ▸ hfirst))
    (fun ⟨hp, hq⟩ => hwords (hp ▸ hq ▸ hfirst.symm))

private def amplitude : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)

private theorem amplitude_star : star amplitude = amplitude := Complex.conj_ofReal _

private theorem amplitude_mul_self : amplitude * amplitude = 1 / 2 := by
  unfold amplitude
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

private def twoPoint (u v : a) (c d : ℂ) : a → ℂ := Pi.single u c + Pi.single v d

private theorem twoPoint_dot (u v : a) (huv : u ≠ v) (c d e f : ℂ) :
    star (twoPoint u v c d) ⬝ᵥ twoPoint u v e f = star c * e + star d * f := by
  rw [show twoPoint u v e f = Pi.single u e + Pi.single v f from rfl,
    dotProduct_add, dotProduct_single, dotProduct_single]
  simp [twoPoint, Pi.star_apply, huv, huv.symm]

private theorem twoPoint_norm (u v : a) (huv : u ≠ v) (flip : Bool) :
    star (twoPoint u v amplitude (phase v flip v * amplitude)) ⬝ᵥ
      twoPoint u v amplitude (phase v flip v * amplitude) = 1 := by
  rw [twoPoint_dot u v huv, star_mul, phase_star, amplitude_star]
  calc
    _ = (amplitude * amplitude) +
          (phase v flip v * phase v flip v) * (amplitude * amplitude) := by ring
    _ = 1 := by rw [phase_mul_self, amplitude_mul_self]; norm_num

omit [Fintype ι] [DecidableEq ι] in
/-- A mixed computational word exists whenever there are at least two sites. -/
private theorem exists_other_word [Nontrivial ι] :
    ∃ w : Bits ι, w ≠ zeroWord ∧ w ≠ oneWord := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  let w : Bits ι := fun x => decide (x = i)
  refine ⟨w, ?_, ?_⟩
  · intro h
    have h' := congrFun h i
    simp [w, zeroWord] at h'
  · intro h
    have h' := congrFun h j
    simp [w, oneWord, hij.symm] at h'

omit [Fintype ι] [DecidableEq ι] in
private theorem zeroWord_ne_oneWord [Nonempty ι] :
    (zeroWord : Bits ι) ≠ oneWord := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h' := congrFun h i
  cases h'

/-- The pure input on one vector in each block gives a diagonal mixed output. -/
theorem mixed_output (u v w : a) (hwu : w ≠ u) (hwv : w ≠ v) (flip : Bool) :
    ∃ ρ : DensityState a, IsPure ρ ∧
      CStarMatrix.ofMatrix.symm ((hiddenChannel u v flip).toCompletelyPositiveMap ρ.1) =
        diagonal (fun x => if x = u ∨ x = w then (1 / 2 : ℂ) else 0) := by
  let t := twoPoint u w amplitude amplitude
  have ht : star t ⬝ᵥ t = 1 := by
    simpa [t, phase] using twoPoint_norm u w hwu.symm false
  refine ⟨pureState t ht, ⟨t, rfl⟩, ?_⟩
  ext x y
  change (hiddenChannel u v flip).toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (vecMulVec t (star t))) x y = _
  have htpoint (i : a) : t i = if i = u ∨ i = w then amplitude else 0 := by
    by_cases hi : i = u ∨ i = w
    · rcases hi with rfl | rfl <;> simp [t, twoPoint, hwu, hwu.symm]
    · simp [t, twoPoint, hi, Ne.symm (not_or.mp hi).1, Ne.symm (not_or.mp hi).2]
  rw [hiddenChannel_entry]
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, htpoint]
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = u ∨ x = w
    · simp only [hx, ite_true, Matrix.diagonal_apply_eq, amplitude_star]
      calc
        _ = (phase v flip x * phase v flip x) * (amplitude * amplitude) := by ring
        _ = 1 / 2 := by rw [phase_mul_self, amplitude_mul_self, one_mul]
    · simp [hx]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    by_cases hx : x = u ∨ x = w <;> by_cases hy : y = u ∨ y = w
    · have hb : inBlock u v x ≠ inBlock u v y := by
        rcases hx with hx | hx <;> rcases hy with hy | hy <;>
          simp_all [inBlock]
      simp [hb]
    all_goals simp [hx, hy]

private theorem mixed_diagonal_rank (u w : a) (hwu : w ≠ u) :
    (diagonal (fun x => if x = u ∨ x = w then (1 / 2 : ℂ) else 0)).rank = 2 := by
  let f : a → ℂ := fun x => if x = u ∨ x = w then 1 / 2 else 0
  have hf (x : a) : f x ≠ 0 ↔ x = u ∨ x = w := by
    by_cases hx : x = u ∨ x = w <;> simp [f, hx]
  let e : Bool ≃ {x // f x ≠ 0} :=
    { toFun := fun b => if b then ⟨u, (hf u).2 (Or.inl rfl)⟩ else ⟨w, (hf w).2 (Or.inr rfl)⟩
      invFun := fun x => decide (x.val = u)
      left_inv := by intro b; cases b <;> simp [hwu]
      right_inv := by
        intro ⟨x, hx⟩
        rcases (hf x).1 hx with rfl | rfl <;> simp [hwu] }
  rw [Matrix.rank_diagonal]
  exact (Fintype.card_congr e).symm.trans (by simp)

omit [DecidableEq a] in
private theorem sandwich_rank_le_one (K : Matrix a a ℂ) (v : a → ℂ) :
    (K * vecMulVec v (star v) * Kᴴ).rank ≤ 1 := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  exact Matrix.rank_vecMulVec_le _ _

/-- A finite Kraus representation with exactly `n` slots, including possible zero operators. -/
def HasKrausCount (C : QuantumChannel a a) (n : ℕ) : Prop :=
  ∃ K : Fin n → Matrix a a ℂ, ∀ X : Matrix a a ℂ,
    CStarMatrix.ofMatrix.symm (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      ∑ j, K j * X * (K j)ᴴ

theorem hiddenChannel_minimum_kraus_count (u v w : a) (hwu : w ≠ u) (hwv : w ≠ v)
    (flip : Bool) : IsLeast {n | HasKrausCount (hiddenChannel u v flip) n} 2 := by
  constructor
  · refine ⟨fun j => kraus u v flip (decide (j = 1)), fun X => ?_⟩
    rw [hiddenChannel_kraus, Fintype.sum_bool, Fin.sum_univ_two]
    simp [add_comm]
  · intro n hn
    change HasKrausCount (hiddenChannel u v flip) n at hn
    obtain ⟨K, hK⟩ := hn
    obtain ⟨ρ, ⟨ψ, hψ⟩, hρ⟩ := mixed_output u v w hwu hwv flip
    rw [hψ] at hρ
    have hr := congrArg Matrix.rank ((hK (vecMulVec ψ (star ψ))).symm.trans hρ)
    rw [mixed_diagonal_rank _ _ hwu] at hr
    match n with
    | 0 => simp at hr
    | 1 =>
      have hle := sandwich_rank_le_one (K 0) ψ
      rw [Fin.sum_univ_one] at hr
      omega
    | n + 2 => omega

theorem minimum_kraus_count [Nontrivial ι] (flip : Bool) :
    IsLeast {n | HasKrausCount (channel (ι := ι) flip) n} 2 := by
  obtain ⟨w, hwu, hwv⟩ := exists_other_word (ι := ι)
  exact hiddenChannel_minimum_kraus_count zeroWord oneWord w hwu hwv flip

private def ghzVector (u v : a) (flip : Bool) : Unit × a → ℂ :=
  twoPoint ((), u) ((), v) amplitude (phase v flip v * amplitude)

private theorem ghzVector_norm (u v : a) (huv : u ≠ v) (flip : Bool) :
    star (ghzVector u v flip) ⬝ᵥ ghzVector u v flip = 1 := by
  unfold ghzVector
  simpa only [phase, and_true] using
    twoPoint_norm ((), u) ((), v) (fun h => huv (congrArg Prod.snd h)) flip

omit [Fintype a] in
private theorem ghzVector_zero (u v : a) (flip : Bool) (x : a) (hx : ¬ (x = u ∨ x = v)) :
    ghzVector u v flip ((), x) = 0 := by
  simp [ghzVector, twoPoint, Ne.symm (not_or.mp hx).1, Ne.symm (not_or.mp hx).2]

omit [Fintype a] in
private theorem ghzVector_phase (u v : a) (huv : u ≠ v) (flip : Bool) (x : a) :
    ghzVector u v flip ((), x) = phase v flip x * ghzVector u v false ((), x) := by
  by_cases hx : x = u ∨ x = v
  · rcases hx with rfl | rfl
    · simp [ghzVector, twoPoint, phase, huv]
    · have h : phase x false x = 1 := by simp [phase]
      simp [ghzVector, twoPoint, huv.symm, h]
  · simp [ghzVector_zero _ _ _ _ hx]

/-- The two relative phases of the GHZ state, with a trivial reference register. -/
def ghzState (u v : a) (huv : u ≠ v) (flip : Bool) : DensityState (Unit × a) :=
  pureState (ghzVector u v flip) (ghzVector_norm u v huv flip)

theorem ghz_output (u v : a) (huv : u ≠ v) (flip : Bool) :
    referenceState (hiddenChannel u v flip) (ghzState u v huv false) =
      ghzState u v huv flip := by
  apply Subtype.ext
  ext ⟨⟨⟩, x⟩ ⟨⟨⟩, y⟩
  change referenceMatrix (hiddenChannel u v flip)
    (vecMulVec (ghzVector u v false) (star (ghzVector u v false))) ((), x) ((), y) = _
  rw [referenceMatrix_apply]
  let X : Matrix a a ℂ := fun i j =>
    vecMulVec (ghzVector u v false) (star (ghzVector u v false)) ((), i) ((), j)
  change (hiddenChannel u v flip).toCompletelyPositiveMap (CStarMatrix.ofMatrix X) x y = _
  rw [hiddenChannel_entry]
  change (if inBlock u v x = inBlock u v y then
    phase v flip x * (ghzVector u v false ((), x) * star (ghzVector u v false ((), y))) *
      phase v flip y else 0) =
    ghzVector u v flip ((), x) * star (ghzVector u v flip ((), y))
  by_cases hx : x = u ∨ x = v
  · by_cases hy : y = u ∨ y = v
    · rw [ghzVector_phase u v huv flip x, ghzVector_phase u v huv flip y, star_mul, phase_star]
      simp only [inBlock, hx, hy, decide_true, ↓reduceIte]
      ring
    · simp [ghzVector_zero _ _ _ _ hy]
  · simp [ghzVector_zero _ _ _ _ hx]

private theorem ghz_orthogonal (u v : a) (huv : u ≠ v) :
    star (ghzVector u v false) ⬝ᵥ ghzVector u v true = 0 := by
  unfold ghzVector
  rw [twoPoint_dot _ _ (fun h => huv (congrArg Prod.snd h))]
  simp only [phase, Bool.false_eq_true, false_and, ↓reduceIte, one_mul,
    true_and, neg_one_mul, amplitude_star]
  ring

/-- The GHZ input witnesses the largest possible unhalved diamond distance. -/
theorem hiddenChannel_maximal_diamond (u v : a) (huv : u ≠ v) :
    diamondDistance (hiddenChannel u v false) (hiddenChannel u v true) = 2 := by
  apply le_antisymm
  · exact diamondDistance_le _ _ (by norm_num) fun _ => referenceError_le_two _ _
  let ρ := ghzState u v huv false
  let P (flip : Bool) := vecMulVec (ghzVector u v flip) (star (ghzVector u v flip))
  have horth : P false * P true = 0 := by
    simp [P, Matrix.vecMulVec_mul_vecMulVec, ghz_orthogonal u v huv]
  have hpos (flip : Bool) : (P flip).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have htrace (flip : Bool) : (P flip).trace = 1 := (ghzState u v huv flip).2.2
  have h := referenceError_le_diamond (hiddenChannel u v false) (hiddenChannel u v true) ρ
  unfold referenceError at h
  rw [ghz_output u v huv false, ghz_output u v huv true] at h
  change traceNorm (P false - P true) ≤ _ at h
  rwa [traceNorm_sub_orthogonal _ _ (hpos false) (hpos true) horth, htrace, htrace,
    Complex.one_re, one_add_one_eq_two] at h

theorem maximal_diamond [Nonempty ι] :
    diamondDistance (channel (ι := ι) false) (channel true) = 2 :=
  hiddenChannel_maximal_diamond _ _ zeroWord_ne_oneWord

/-- A square CPTP map with one Kraus operator is a unitary conjugation. -/
theorem exists_unitary_of_one_kraus (C : QuantumChannel a a) (h : HasKrausCount C 1) :
    ∃ U : unitaryGroup a ℂ, C = conjugation U := by
  obtain ⟨K, hK⟩ := h
  simp only [Fin.sum_univ_one] at hK
  have hU : (K 0)ᴴ * K 0 = 1 := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    have ht := C.trace_preserving (CStarMatrix.ofMatrix X)
    change (CStarMatrix.ofMatrix.symm
      (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix X))).trace = X.trace at ht
    rw [hK, Matrix.trace_mul_comm, ← Matrix.mul_assoc] at ht
    simpa only [Matrix.one_mul] using ht
  let U : unitaryGroup a ℂ := ⟨K 0, Matrix.mem_unitaryGroup_iff'.mpr hU⟩
  refine ⟨U, channel_ext fun X => CStarMatrix.ofMatrix.symm.injective ?_⟩
  rw [← CStarMatrix.ofMatrix.apply_symm_apply X, hK, conjugation_apply]

section RankOneThreshold

variable {sites : Type} [Fintype sites] [DecidableEq sites]

private theorem singleton_output_eq_transfer (i : sites)
    (C D : QuantumChannel (Bits sites) (Bits sites))
    (h : (discard (split {i})).comp C = (discard (split {i})).comp D) :
    (discard (splitSite (fun _ : sites => Bool) i)).comp C =
      (discard (splitSite (fun _ : sites => Bool) i)).comp D := by
  let e : ({j : sites // j ≠ i} → Bool) ≃ Discarded {i} :=
    Equiv.piCongrLeft' (fun _ => Bool) (Equiv.subtypeEquivRight (fun j => by simp))
  let keep (b : Bool) : Kept ({i} : Finset sites) := fun _ => b
  have he (z : {j : sites // j ≠ i} → Bool) (b : Bool) :
      (split {i}).symm (e z, keep b) = (splitSite (fun _ : sites => Bool) i).symm (z, b) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [split, splitSite, keep, Equiv.piEquivPiSubtypeProd, Equiv.piSplitAt]
    · simp only [split, splitSite, Equiv.symm_trans_apply, Equiv.prodComm_symm,
        Equiv.prodComm_apply, Equiv.piEquivPiSubtypeProd_symm_apply,
        Equiv.piSplitAt_symm_apply, Finset.mem_singleton, dite_eq_right hj]
      rfl
  have hentry (B : QuantumChannel (Bits sites) (Bits sites))
      (X : CStarMatrix (Bits sites) (Bits sites) ℂ) (x y : Bool) :
      ((discard (splitSite (fun _ : sites => Bool) i)).comp B).toCompletelyPositiveMap X x y =
      ((discard (split {i})).comp B).toCompletelyPositiveMap X (keep x) (keep y) := by
    simp only [QuantumChannel.comp_apply]
    let Y := CStarMatrix.ofMatrix.symm (B.toCompletelyPositiveMap X)
    rw [← CStarMatrix.ofMatrix.apply_symm_apply (B.toCompletelyPositiveMap X)]
    have h₁ := congrArg (fun M : Matrix Bool Bool ℂ => M x y)
      (discard_apply (splitSite (fun _ : sites => Bool) i) Y)
    have h₂ := congrArg (fun M : Matrix (Kept {i}) (Kept {i}) ℂ => M (keep x) (keep y))
      (discard_apply (split {i}) Y)
    change (discard (splitSite (fun _ : sites => Bool) i)).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix Y) x y = _ at h₁
    change (discard (split {i})).toCompletelyPositiveMap
        (CStarMatrix.ofMatrix Y) (keep x) (keep y) = _ at h₂
    rw [h₁, h₂]
    simp only [partialTraceFirst, Matrix.submatrix_apply]
    rw [← e.sum_comp (fun z => Y ((split {i}).symm (z, keep x)) ((split {i}).symm (z, keep y)))]
    simp only [he]
  apply channel_ext
  intro X
  ext x y
  rw [hentry C, hentry D, h]

/-- Agreement of all proper output channels determines a one-Kraus channel uniquely
among one-Kraus channels on the same register. -/
theorem one_kraus_eq_of_proper_output_eq [Nontrivial sites]
    (C D : QuantumChannel (Bits sites) (Bits sites))
    (hC : HasKrausCount C 1) (hD : HasKrausCount D 1)
    (h : ∀ s : Finset sites, s ≠ Finset.univ →
      (discard (split s)).comp C = (discard (split s)).comp D) : C = D := by
  obtain ⟨U, rfl⟩ := exists_unitary_of_one_kraus C hC
  obtain ⟨V, rfl⟩ := exists_unitary_of_one_kraus D hD
  apply conjugation_eq_of_siteChannel_eq (fun _ : sites => Bool)
  intro i
  obtain ⟨j, hj⟩ := exists_ne i
  have hs : ({i} : Finset sites) ≠ Finset.univ := by
    intro he
    have hm : j ∈ ({i} : Finset sites) := by rw [he]; exact Finset.mem_univ _
    exact hj (Finset.mem_singleton.mp hm)
  exact singleton_output_eq_transfer i _ _ (h {i} hs)

end RankOneThreshold

theorem proper_output_reference_eq (s : Finset ι) (hs : s ≠ Finset.univ)
    {r : Type*} [Fintype r] [DecidableEq r]
    (X : Matrix (r × Bits ι) (r × Bits ι) ℂ) :
    referenceMatrix ((discard (split s)).comp (channel false)) X =
      referenceMatrix ((discard (split s)).comp (channel true)) X :=
  congrArg (fun C => referenceMatrix C X) (proper_output_eq s hs)

/-- The explicit unital rank-two pair agrees on every proper output and has diamond distance two. -/
theorem rank_two_ambiguity [Nontrivial ι] :
    (∀ flip, IsLeast {n | HasKrausCount (channel (ι := ι) flip) n} 2 ∧
      (channel (ι := ι) flip).toCompletelyPositiveMap 1 = 1) ∧
    (∀ s : Finset ι, s ≠ Finset.univ →
      (discard (split s)).comp (channel false) = (discard (split s)).comp (channel true)) ∧
    diamondDistance (channel (ι := ι) false) (channel true) = 2 :=
  ⟨fun flip => ⟨minimum_kraus_count flip, hiddenChannel_unital zeroWord oneWord flip⟩,
    proper_output_eq, maximal_diamond⟩

end UnitaryReconstruction.RankTwoHiddenProcess
