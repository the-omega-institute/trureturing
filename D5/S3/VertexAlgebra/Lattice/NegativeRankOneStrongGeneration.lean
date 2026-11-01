/- GID: D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-state failure of finite negative-word strong generation in negative rank one. -/

import D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy
import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
import D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus

/-!
Every finite family in the actual negative rank-one carrier has a bounded
charge palette. The charge-q oscillator-constant functional, q beyond that
palette, annihilates every right-nested word of negative modes.

proof_shape: negative_rank_one_no_finite_strong_generation: content
admission_basis: escape-witness
escape_witness: palette_word_zero uses strong induction on unrestricted word
length. Moving the first nonnegative-charge factor across a negative prefix
uses the actual finite mode commutator; each correction has one fewer factor
and remains in the same charge palette. The final proper-span proof consumes
this induction through paletteSpan_le_ker and the arbitrary mixed-state
decomposition, while the charge-q ground state has coefficient one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.NegativeRankOneStrongGeneration

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticePositiveEnergy LatticeCoefficientEnergy
open scoped BigOperators VertexOperator

noncomputable section

/- The coefficient of the oscillator constant in a fixed charge sector. -/
def groundCoefficient (D : LatticeData) (q : Charge D) : Carrier D →ₗ[ℂ] ℂ :=
  (Finsupp.lapply (q, 0)).comp (carrierCoeffEquiv D).toLinearMap

@[simp] private theorem groundCoefficient_apply (D : LatticeData) (q : Charge D)
    (v : Carrier D) :
    groundCoefficient D q v = (v q).coeff 0 := by
  rfl

/- This is the exact projection consequence of the original all-state grading;
   it applies to arbitrary oscillator polynomials and arbitrary finite charge
   mixtures, with no positivity or global lower-bound premise. -/
private theorem groundCoefficient_mode_eq_zero_of_grade_mismatch
    (D : LatticeData) (m n k : ℤ) (q : Charge D) (u v : Carrier D)
    (hu : u ∈ grade D m) (hv : v ∈ grade D n)
    (hneq : energy D (q, 0) ≠ m + n - k - 1) :
    groundCoefficient D q (((Y D u)[[k]]) v) = 0 := by
  have hout := actual_mode_grade D m n k u v hu hv
  have hz := (mem_grade_iff D (m + n - k - 1) _).mp hout (q, 0) hneq
  exact hz

/- The strict inequality which drives the positive-charge outer insertion in
   G=-2d.  The factors r,t are arbitrary oscillator degrees; no lower bound
   on the total charge energy is used. -/
private theorem negative_rank_one_outer_energy_mismatch
    (d s q r t k : ℤ)
    (hd : 0 < d) (hs : 0 < s) (hsq : s < q)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hk : k < 0) :
    -d * q ^ 2 ≠ (r - d * s ^ 2) + (t - d * (q - s) ^ 2) - k - 1 := by
  intro h
  have hqs : 0 < q - s := by omega
  have hprod : 0 < 2 * d * s * (q - s) := by positivity
  nlinarith

/-- The actual even rank-one datum; positivity of d is used only in the theorem. -/
abbrev datum (d : ℤ) : LatticeData where
  rank := 1
  G := fun _ _ => -2 * (d : ℤ)
  symmetric := by intros; rfl
  even_diagonal := by intro i; exact ⟨-(d : ℤ), by ring⟩

def charge (d : ℤ) (s : ℤ) : Charge (datum d) := fun _ => s

@[simp] private theorem charge_zero (d : ℤ) : charge d 0 = 0 := rfl

private theorem charge_eq (d : ℤ) (a : Charge (datum d)) :
    a = charge d (a 0) := by
  funext i
  exact congrArg a (Subsingleton.elim i 0)

@[simp] private theorem charge_inj (d : ℤ) (s t : ℤ) :
    charge d s = charge d t ↔ s = t := by
  constructor
  · intro h; exact congrFun h 0
  · rintro rfl; rfl

private theorem bilinear_charge (d : ℤ) (s t : ℤ) :
    bilinear (datum d) (charge d s) (charge d t) = -2 * (d : ℤ) * s * t := by
  change (∑ _i : Fin 1, ∑ _j : Fin 1, s * (-2*d) * t) = -2*d*s*t
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  ring

private theorem charge_energy (d : ℤ) (s : ℤ) :
    chargeEnergy (datum d) (charge d s) = -(d : ℤ) * s ^ 2 := by
  have h := two_chargeEnergy (datum d) (charge d s)
  rw [bilinear_charge] at h
  nlinarith

private theorem basis_energy (d : ℤ) (s : ℤ) (e : Exponent (datum d)) :
    energy (datum d) (charge d s, e) =
      (oscillatorEnergy e : ℤ) - (d : ℤ) * s ^ 2 := by
  simp [energy, charge_energy]; ring

private theorem basis_grade (D : LatticeData) (a : Label D) :
    carrierBasis D a ∈ grade D (energy D a) := by
  rw [grade_eq_span]
  exact Submodule.subset_span ⟨a, rfl, rfl⟩

private def mode (D : LatticeData) (k : ℤ) :
    Carrier D →ₗ[ℂ] Module.End ℂ (Carrier D) where
  toFun u := ((Y D u)[[k]])
  map_add' u v := by simp
  map_smul' c u := by simp

private theorem basis_outer_zero (d : ℤ) (hd : 0 < d) (s q k : ℤ)
    (hs : 0 ≤ s) (hsq : s < q) (hk : k < 0)
    (e : Exponent (datum d)) (he : 0 < s ∨ e ≠ 0)
    (a : Label (datum d)) :
    groundCoefficient (datum d) (charge d q)
      (mode (datum d) k (carrierBasis (datum d) (charge d s, e))
        (carrierBasis (datum d) a)) = 0 := by
  classical
  obtain ⟨β, f⟩ := a
  by_cases hb : β = charge d (q - s)
  · subst β
    apply groundCoefficient_mode_eq_zero_of_grade_mismatch (datum d)
      (energy (datum d) (charge d s, e))
      (energy (datum d) (charge d (q-s), f)) k (charge d q)
      _ _ (basis_grade _ _) (basis_grade _ _)
    rw [basis_energy, basis_energy, basis_energy]
    simp only [show oscillatorEnergy (0 : Exponent (datum d)) = 0 by
      simp [oscillatorEnergy], Nat.cast_zero, zero_sub]
    rcases he with hp | hp
    · simpa only [neg_mul] using negative_rank_one_outer_energy_mismatch (d : ℤ) s q
        (oscillatorEnergy e) (oscillatorEnergy f) k (by omega) hp hsq
        (by positivity) (by positivity) hk
    · by_cases hp' : 0 < s
      · simpa only [neg_mul] using negative_rank_one_outer_energy_mismatch (d : ℤ) s q
          (oscillatorEnergy e) (oscillatorEnergy f) k (by omega) hp' hsq
          (by positivity) (by positivity) hk
      · have hz : s = 0 := by omega
        have hr : 0 < oscillatorEnergy e :=
          Nat.pos_of_ne_zero (fun h => hp ((oscillatorEnergy_eq_zero_iff _ _).mp h))
        have hr' : (0 : ℤ) < oscillatorEnergy e := by exact_mod_cast hr
        subst s
        have ht : (0 : ℤ) ≤ oscillatorEnergy f := by positivity
        intro h
        nlinarith
  · rw [carrierBasis_apply, carrierBasis_apply]
    change groundCoefficient (datum d) (charge d q)
      (((Y (datum d) (Finsupp.single (charge d s) (MvPolynomial.monomial e 1)))[[k]])
        (Finsupp.single β (MvPolynomial.monomial f 1))) = 0
    rw [LatticeSectorIntertwiner.charge_homogeneity, groundCoefficient_apply,
      Finsupp.single_eq_of_ne']
    · simp
    · intro h
      apply hb
      ext i
      have hi := congrFun h i
      change s + β i = q at hi
      change β i = q - s
      omega

private theorem outer_positive (d : ℤ) (hd : 0 < d) (s q k : ℤ)
    (hs : 0 < s) (hsq : s < q) (hk : k < 0)
    (p : Oscillator (datum d)) (v : Carrier (datum d)) :
    groundCoefficient (datum d) (charge d q)
      (mode (datum d) k (Finsupp.single (charge d s) p) v) = 0 := by
  let L : Oscillator (datum d) →ₗ[ℂ] Carrier (datum d) →ₗ[ℂ] ℂ :=
    { toFun := fun p => (groundCoefficient (datum d) (charge d q)).comp
        (mode (datum d) k (Finsupp.single (charge d s) p))
      map_add' := by intros; ext; simp [mode]
      map_smul' := by intros; ext; simp [mode] }
  have hL : L = 0 := by
    apply (MvPolynomial.basisMonomials (Index (datum d)) ℂ).ext
    intro e
    apply (carrierBasis (datum d)).ext
    intro a
    change groundCoefficient (datum d) (charge d q)
      (mode (datum d) k (Finsupp.single (charge d s) (MvPolynomial.monomial e 1))
        (carrierBasis (datum d) a)) = 0
    simpa only [carrierBasis_apply] using
      basis_outer_zero d hd s q k hs.le hsq hk e (Or.inl hs) a
  exact congrArg (fun f => f p v) hL

private theorem outer_zero (d : ℤ) (hd : 0 < d) (q k : ℤ)
    (hq : 0 < q) (hk : k < 0)
    (p : Oscillator (datum d)) (v : Carrier (datum d)) :
    groundCoefficient (datum d) (charge d q)
      (mode (datum d) k (Finsupp.single (charge d 0) p) v) =
      p.coeff 0 * (if k = -1 then groundCoefficient (datum d) (charge d q) v else 0) := by
  classical
  let L : Oscillator (datum d) →ₗ[ℂ] Carrier (datum d) →ₗ[ℂ] ℂ :=
    { toFun := fun p => (groundCoefficient (datum d) (charge d q)).comp
        (mode (datum d) k (Finsupp.single (charge d 0) p))
      map_add' := by intros; ext; simp [mode]
      map_smul' := by intros; ext; simp [mode] }
  let R : Oscillator (datum d) →ₗ[ℂ] Carrier (datum d) →ₗ[ℂ] ℂ :=
    (MvPolynomial.lcoeff ℂ 0).smulRight
      (if k = -1 then groundCoefficient (datum d) (charge d q) else 0)
  have hL : L = R := by
    apply (MvPolynomial.basisMonomials (Index (datum d)) ℂ).ext
    intro e
    apply (carrierBasis (datum d)).ext
    intro a
    by_cases he : e = 0
    · subst e
      change groundCoefficient (datum d) (charge d q)
        (mode (datum d) k (Finsupp.single (charge d 0) (MvPolynomial.monomial 0 1))
          (carrierBasis (datum d) a)) = _
      have hc : Finsupp.single (charge d 0)
          (MvPolynomial.monomial (0 : Exponent (datum d)) (1 : ℂ)) = vacuum (datum d) := by
        simp [vacuum]
      rw [hc]
      by_cases hk' : k = -1 <;>
        simp [mode, stateField_vacuum, identity_modes, hk', R,
          MvPolynomial.lcoeff]
    · have hz := basis_outer_zero d hd 0 q k (by omega) hq hk e (Or.inr he) a
      rw [carrierBasis_apply] at hz
      change groundCoefficient (datum d) (charge d q)
        (mode (datum d) k (Finsupp.single (charge d 0) (MvPolynomial.monomial e 1))
          (carrierBasis (datum d) a)) = _
      rw [hz]
      simp [R, MvPolynomial.lcoeff, MvPolynomial.coeff_monomial, he]
  have hh := congrArg (fun f => f p v) hL
  by_cases hk' : k = -1 <;> simpa [L, R, MvPolynomial.lcoeff, hk'] using hh

/-- A palette letter retains an arbitrary oscillator polynomial and integer mode. -/
private structure Letter (d : ℤ) where
  weight : ℤ
  polynomial : Oscillator (datum d)
  index : ℤ

private def letterState {d : ℤ} (a : Letter d) : Carrier (datum d) :=
  Finsupp.single (charge d a.weight) a.polynomial

private def wordOperator {d : ℤ} : List (Letter d) → Module.End ℂ (Carrier (datum d))
  | [] => LinearMap.id
  | a :: w => mode (datum d) a.index (letterState a) * wordOperator w

private def paletteWord {d : ℤ} (w : List (Letter d)) : Carrier (datum d) :=
  wordOperator w (vacuum (datum d))

private def Good {d : ℤ} (M : ℤ) (w : List (Letter d)) : Prop :=
  ∀ a ∈ w, -M ≤ a.weight ∧ a.weight ≤ M ∧ a.index < 0

private theorem wordOperator_append {d : ℤ} (l r : List (Letter d)) :
    wordOperator (l ++ r) = wordOperator l * wordOperator r := by
  induction l with
  | nil => ext v; rfl
  | cons a l ih => simp [wordOperator, ih, mul_assoc]

private def wordCharge {d : ℤ} : List (Letter d) → ℤ
  | [] => 0
  | a :: w => a.weight + wordCharge w

private theorem word_charge {d : ℤ} (w : List (Letter d)) :
    ∃ p : Oscillator (datum d), paletteWord w = Finsupp.single (charge d (wordCharge w)) p := by
  induction w with
  | nil => exact ⟨1, rfl⟩
  | cons a w ih =>
    obtain ⟨p, hp⟩ := ih
    have h := LatticeSectorIntertwiner.charge_homogeneity (datum d)
      (charge d a.weight) (charge d (wordCharge w)) a.polynomial p a.index
    refine ⟨(mode (datum d) a.index (letterState a)
      (Finsupp.single (charge d (wordCharge w)) p))
        (charge d (a.weight + wordCharge w)), ?_⟩
    change mode (datum d) a.index (letterState a) (paletteWord w) = _
    rw [hp]
    exact h

private theorem all_negative_zero {d : ℤ} (q : ℤ) (hq : 0 < q)
    (w : List (Letter d)) (hw : ∀ a ∈ w, a.weight < 0) :
    groundCoefficient (datum d) (charge d q) (paletteWord w) = 0 := by
  have hnonpos : ∀ w : List (Letter d), (∀ a ∈ w, a.weight < 0) → wordCharge w ≤ 0 := by
    intro w
    induction w with
    | nil => simp [wordCharge]
    | cons a w ih =>
      intro hw
      have ha := hw a (by simp)
      have ht := ih (fun b hb => hw b (by simp [hb]))
      change a.weight + wordCharge w ≤ 0
      omega
  have hc := hnonpos w hw
  obtain ⟨p, hp⟩ := word_charge w
  rw [hp, groundCoefficient_apply, Finsupp.single_eq_of_ne']
  · simp
  · simpa using (show wordCharge w ≠ q by omega)

private def correction {d : ℤ} (b a : Letter d) (j : ℕ) : Letter d where
  weight := b.weight + a.weight
  polynomial := (mode (datum d) (j : ℤ) (letterState b) (letterState a))
    (charge d (b.weight + a.weight))
  index := b.index + a.index - j

private theorem correction_state {d : ℤ} (b a : Letter d) (j : ℕ) :
    letterState (correction b a j) =
      LatticeAllStateReconstruction.mu (datum d) (letterState b) j (letterState a) := by
  exact (LatticeSectorIntertwiner.charge_homogeneity (datum d)
    (charge d b.weight) (charge d a.weight) b.polynomial a.polynomial j).symm

private theorem correction_good {d : ℤ} (M : ℤ) (b a : Letter d)
    (hb : -M ≤ b.weight ∧ b.weight ≤ M ∧ b.index < 0)
    (ha : -M ≤ a.weight ∧ a.weight ≤ M ∧ a.index < 0)
    (hbn : b.weight < 0) (han : 0 ≤ a.weight) (j : ℕ) :
    -M ≤ (correction b a j).weight ∧ (correction b a j).weight ≤ M ∧
      (correction b a j).index < 0 := by
  dsimp [correction]
  omega

private theorem move_nonnegative (d : ℤ) (hd : 0 < d) (M q : ℤ)
    (_hM : 0 ≤ M) (hq : M < q) (N : ℕ)
    (short : ∀ w : List (Letter d), w.length < N → Good M w →
      groundCoefficient (datum d) (charge d q) (paletteWord w) = 0)
    (l : List (Letter d)) :
    ∀ (a : Letter d) (r : List (Letter d)), (l ++ a :: r).length = N →
      Good M (l ++ a :: r) → (∀ b ∈ l, b.weight < 0) → 0 ≤ a.weight →
      groundCoefficient (datum d) (charge d q) (paletteWord (l ++ a :: r)) = 0 := by
  classical
  induction l using List.reverseRecOn with
  | nil =>
    intro a r hn hg hl ha
    have ha' := hg a (by simp)
    have hr : Good M r := fun b hb => hg b (by simp [hb])
    change groundCoefficient (datum d) (charge d q)
      (mode (datum d) a.index (letterState a) (paletteWord r)) = 0
    by_cases hp : 0 < a.weight
    · exact outer_positive d hd a.weight q a.index hp (by omega) ha'.2.2
        a.polynomial (paletteWord r)
    · have hz : a.weight = 0 := by omega
      unfold letterState
      rw [hz, outer_zero d hd q a.index (by omega) ha'.2.2]
      have hs := short r (by simp only [List.nil_append, List.length_cons] at hn; omega) hr
      simp [hs]
  | append_singleton l b ih =>
    intro a r hn hg hl ha
    have hb := hg b (by simp)
    have ha' := hg a (by simp)
    have hbn := hl b (by simp)
    have hln : ∀ c ∈ l, c.weight < 0 := fun c hc => hl c (by simp [hc])
    have hswap : Good M (l ++ a :: b :: r) := by
      intro c hc
      apply hg c
      simpa only [List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false, false_or, or_assoc, or_left_comm, or_comm] using hc
    have swapped := ih a (b :: r) (by simpa [List.length_append] using hn)
      hswap hln ha
    let F : Module.End ℂ (Carrier (datum d)) →ₗ[ℂ] ℂ :=
      ((groundCoefficient (datum d) (charge d q)).comp (wordOperator l)).comp
        (LinearMap.applyₗ (paletteWord r))
    have corrections : F (∑ᶠ j : ℕ,
        LatticeActualStateFieldCalculus.commutatorTerm (datum d)
          (letterState b) (letterState a) b.index a.index j) = 0 := by
      rw [map_finsum F (LatticeActualStateFieldCalculus.commutator_terms_finite
        (datum d) (letterState b) (letterState a) b.index a.index)]
      apply finsum_eq_zero_of_forall_eq_zero
      intro j
      have hj : Good M (l ++ correction b a j :: r) := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hg c (by simp [hc])
        · rcases List.mem_cons.mp hc with hc | hc
          · subst c; exact correction_good M b a hb ha' hbn ha j
          · exact hg c (by simp [hc])
      have hz := short (l ++ correction b a j :: r)
        (by simp only [List.length_append, List.length_cons] at hn ⊢
            omega) hj
      unfold LatticeActualStateFieldCalculus.commutatorTerm
      rw [← correction_state]
      change F (StateFieldResidueReconstruction.integerBinomial b.index j •
        mode (datum d) (correction b a j).index (letterState (correction b a j))) = 0
      rw [map_smul]
      have hF : F (mode (datum d) (correction b a j).index
          (letterState (correction b a j))) = 0 := by
        simpa [F, paletteWord, wordOperator_append, wordOperator] using hz
      simp [hF]
    have comm := congrArg F (LatticeActualStateFieldCalculus.mode_commutator
      (datum d) (letterState b) (letterState a) b.index a.index)
    rw [map_sub, corrections] at comm
    have hswapF : F (mode (datum d) a.index (letterState a) *
        mode (datum d) b.index (letterState b)) = 0 := by
      simpa [F, paletteWord, wordOperator_append, wordOperator, mul_assoc] using swapped
    change F (mode (datum d) b.index (letterState b) *
      mode (datum d) a.index (letterState a)) -
      F (mode (datum d) a.index (letterState a) *
        mode (datum d) b.index (letterState b)) = 0 at comm
    rw [hswapF, sub_zero] at comm
    simpa [F, paletteWord, wordOperator_append, wordOperator, mul_assoc] using comm

private theorem split_nonnegative {d : ℤ} (w : List (Letter d))
    (h : ¬ ∀ a ∈ w, a.weight < 0) :
    ∃ l a r, w = l ++ a :: r ∧ (∀ b ∈ l, b.weight < 0) ∧ 0 ≤ a.weight := by
  induction w with
  | nil => simp at h
  | cons b w ih =>
    by_cases hb : 0 ≤ b.weight
    · exact ⟨[], b, w, rfl, by simp, hb⟩
    · have ht : ¬ ∀ a ∈ w, a.weight < 0 := by
        intro ht; apply h; intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · omega
        · exact ht a ha
      obtain ⟨l, a, r, hw, hl, ha⟩ := ih ht
      refine ⟨b :: l, a, r, by simp [hw], ?_, ha⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · omega
      · exact hl c hc

private theorem palette_word_zero (d : ℤ) (hd : 0 < d) (M q : ℤ)
    (hM : 0 ≤ M) (hq : M < q) (w : List (Letter d)) (hw : Good M w) :
    groundCoefficient (datum d) (charge d q) (paletteWord w) = 0 := by
  suffices H : ∀ N : ℕ, ∀ w : List (Letter d), w.length = N → Good M w →
      groundCoefficient (datum d) (charge d q) (paletteWord w) = 0 from H _ w rfl hw
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro w hn hg
    by_cases hneg : ∀ a ∈ w, a.weight < 0
    · exact all_negative_zero q (by omega) w hneg
    · obtain ⟨l, a, r, rfl, hl, ha⟩ := split_nonnegative w hneg
      exact move_nonnegative d hd M q hM hq N
        (fun w hw hg => ih w.length hw w rfl hg) l a r hn hg hl ha

private def paletteSpan (d M : ℤ) : Submodule ℂ (Carrier (datum d)) :=
  Submodule.span ℂ {v | ∃ w : List (Letter d), Good M w ∧ paletteWord w = v}

private theorem paletteSpan_le_ker (d : ℤ) (hd : 0 < d) (M q : ℤ)
    (hM : 0 ≤ M) (hq : M < q) :
    paletteSpan d M ≤ LinearMap.ker (groundCoefficient (datum d) (charge d q)) := by
  apply Submodule.span_le.mpr
  rintro v ⟨w, hw, rfl⟩
  exact palette_word_zero d hd M q hM hq w hw

private theorem paletteSpan_closed (d M s k : ℤ)
    (hs : -M ≤ s ∧ s ≤ M) (hk : k < 0)
    (p : Oscillator (datum d)) (v : Carrier (datum d)) (hv : v ∈ paletteSpan d M) :
    mode (datum d) k (Finsupp.single (charge d s) p) v ∈ paletteSpan d M := by
  classical
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    apply Submodule.subset_span
    refine ⟨⟨s,p,k⟩ :: w, ?_, rfl⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨hs.1, hs.2, hk⟩
    · exact hw a ha
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (paletteSpan d M).add_mem ihx ihy
  | smul c x hx ih => simpa using (paletteSpan d M).smul_mem c ih

/-- Right-nested strictly negative normalized modes of arbitrary actual states. -/
def negativeWord (D : LatticeData) (S : Finset (Carrier D)) :
    List ({u : Carrier D // u ∈ S} × ℕ) → Carrier D
  | [] => vacuum D
  | (a,n) :: w => ((Y D a.1)[[-(n : ℤ)-1]]) (negativeWord D S w)

/-- This is the precise negative-word convention used for strong generation here. -/
def negativeWordSpan (D : LatticeData) (S : Finset (Carrier D)) :
    Submodule ℂ (Carrier D) := Submodule.span ℂ (Set.range (negativeWord D S))

def StronglyGenerates (D : LatticeData) (S : Finset (Carrier D)) : Prop :=
  negativeWordSpan D S = ⊤

private def familyBound (d : ℤ) (S : Finset (Carrier (datum d))) : ℕ :=
  by classical exact S.sup (fun u => u.support.sup (fun α => (α 0).natAbs))

private theorem familyBound_spec (d : ℤ) (S : Finset (Carrier (datum d)))
    (u : Carrier (datum d)) (hu : u ∈ S) (α : Charge (datum d)) (hα : α ∈ u.support) :
    -(familyBound d S : ℤ) ≤ α 0 ∧ α 0 ≤ (familyBound d S : ℤ) := by
  have h₁ := Finset.le_sup (f := fun α : Charge (datum d) => (α 0).natAbs) hα
  have h₂ := Finset.le_sup (f := fun u : Carrier (datum d) =>
    u.support.sup (fun α => (α 0).natAbs)) hu
  have h : (α 0).natAbs ≤ familyBound d S := h₁.trans h₂
  have hz : ((α 0).natAbs : ℤ) ≤ (familyBound d S : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at hz
  exact abs_le.mp hz

private theorem family_mode_closed (d : ℤ) (S : Finset (Carrier (datum d)))
    (u : Carrier (datum d)) (hu : u ∈ S) (k : ℤ) (hk : k < 0)
    (v : Carrier (datum d)) (hv : v ∈ paletteSpan d (familyBound d S)) :
    mode (datum d) k u v ∈ paletteSpan d (familyBound d S) := by
  classical
  have hsum : u = ∑ α ∈ u.support, Finsupp.single α (u α) := by
    simpa only [Finsupp.sum] using u.sum_single.symm
  rw [hsum, map_sum]
  simp only [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro α hα
  have hb := familyBound_spec d S u hu α hα
  rw [charge_eq d α]
  exact paletteSpan_closed d (familyBound d S) (α 0) k hb hk _ v hv

private theorem negativeWord_mem_palette (d : ℤ) (S : Finset (Carrier (datum d)))
    (w : List ({u : Carrier (datum d) // u ∈ S} × ℕ)) :
    negativeWord (datum d) S w ∈ paletteSpan d (familyBound d S) := by
  induction w with
  | nil => exact Submodule.subset_span ⟨[], by simp [Good], rfl⟩
  | cons a w ih =>
    exact family_mode_closed d S a.1.1 a.1.2 (-(a.2 : ℤ)-1) (by omega) _ ih

/-- No finite family of arbitrary mixed-charge oscillator states strongly generates
the actual negative rank-one lattice carrier by right-nested negative modes. -/
theorem negative_rank_one_no_finite_strong_generation (d : ℤ) (hd : 0 < d)
    (S : Finset (Carrier (datum d))) : ¬ StronglyGenerates (datum d) S := by
  change negativeWordSpan (datum d) S ≠ ⊤
  classical
  let M : ℤ := familyBound d S
  let q : ℤ := M + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hq : M < q := by dsimp [q]; omega
  have hle : negativeWordSpan (datum d) S ≤ paletteSpan d M := by
    apply Submodule.span_le.mpr
    rintro v ⟨w, rfl⟩
    exact negativeWord_mem_palette d S w
  have hker := hle.trans (paletteSpan_le_ker d hd M q hM hq)
  intro htop
  have hg : Finsupp.single (charge d q) (1 : Oscillator (datum d)) ∈
      negativeWordSpan (datum d) S := by rw [htop]; trivial
  have hz := hker hg
  change groundCoefficient (datum d) (charge d q)
    (Finsupp.single (charge d q) (1 : Oscillator (datum d))) = 0 at hz
  simp at hz

#print axioms negative_rank_one_no_finite_strong_generation

end
end D5.S3.VertexAlgebra.Lattice.NegativeRankOneStrongGeneration

