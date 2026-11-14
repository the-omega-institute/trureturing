/- GID: D5/S3/Quantum/Routing/HannRouterDephasing
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannRouterDephasing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual loaded router mismatch counts and single-hold dephasing. -/


import D5.S3.Quantum.Routing.HannSpatialQram
import D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent router records on literal spatial QRAM coordinates. -/

open scoped BigOperators ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Routing.HannRouterDephasing

open HannSpatialQram
open ReversibleQram (Address)

/-- The head-first word read from the actual address slots. -/
def addressWord : (n : ℕ) → Address n → List Bool
  | 0, _ => []
  | n + 1, a => a.1 :: addressWord n a.2

/-- Count unequal internal router coordinates, excluding every incident/output rail. -/
def routerMismatch : (n : ℕ) → HannSpatialQram.Tree n → HannSpatialQram.Tree n → ℕ
  | 0, _, _ => 0
  | n + 1, t, u => (if t.2.1 = u.2.1 then 0 else 1) +
      routerMismatch n t.2.2.1 u.2.2.1 + routerMismatch n t.2.2.2 u.2.2.2

private theorem router_mismatch_self (n : ℕ) (t : HannSpatialQram.Tree n) :
    routerMismatch n t t = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [routerMismatch, ih]

private theorem router_mismatch_vacuum (n : ℕ) (a : Address n) :
    routerMismatch n (programmed n a n) (vacuum n) = n ∧
      routerMismatch n (vacuum n) (programmed n a n) = n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      rcases a with ⟨b, a⟩
      have h := ih a
      cases b <;> simp [routerMismatch, programmed, vacuum, encode,
        router_mismatch_self, h.1, h.2, Nat.add_comm]

private theorem address_word_length (n : ℕ) (a : Address n) :
    (addressWord n a).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [addressWord, ih]

private theorem router_mismatch_programmed (n : ℕ) (a a' : Address n) :
    routerMismatch n (programmed n a n) (programmed n a' n) =
      if a = a' then 0 else
        2 * (n - (D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.lcp
          (addressWord n a) (addressWord n a')).length) - 1 := by
  induction n with
  | zero => have h : a = a' := Subsingleton.elim _ _; simp [h, routerMismatch]
  | succ n ih =>
      rcases a with ⟨b, a⟩
      rcases a' with ⟨c, a'⟩
      have hv := router_mismatch_vacuum n a
      have hv' := router_mismatch_vacuum n a'
      have hp := (D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.shortest_pop_append
        (addressWord n a) (addressWord n a')).1.1.length_le
      rw [address_word_length] at hp
      cases b <;> cases c <;>
        simp [routerMismatch, programmed, encode, router_mismatch_self,
          hv.1, hv'.2, addressWord,
          D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.lcp, ih,
          Prod.mk.injEq] <;> omega

/-- The mismatch count is for the actual state after all sequential loads. -/
private theorem loaded_router_mismatch (n : ℕ) (a a' : Address n) (b b' : Bool) :
    routerMismatch n ((load n n) (clean n a b)).2.2
      ((load n n) (clean n a' b')).2.2 =
      if a = a' then 0 else
        2 * (n - (D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.lcp
          (addressWord n a) (addressWord n a')).length) - 1 := by
  rw [show load n n (clean n a b) = loading n a (encode b) n from
    correctness.1 n a (encode b) n (le_refl n),
    show load n n (clean n a' b') = loading n a' (encode b') n from
    correctness.1 n a' (encode b') n (le_refl n)]
  exact router_mismatch_programmed n a a'



/-- One independent four-dimensional environment per internal router. -/
abbrev Environment : ℕ → Type
  | 0 => Unit
  | n + 1 => Option Qutrit × Environment n × Environment n

instance environmentFintype : (n : ℕ) → Fintype (Environment n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := environmentFintype n
             inferInstanceAs (Fintype (Option Qutrit × Environment n × Environment n))

/-- The common environment coordinate is none; the three record coordinates are some s. -/
def localRecord (q : ℝ) (s : Qutrit) : Option Qutrit → ℂ
  | none => (Real.sqrt q : ℂ)
  | some t => if t = s then (Real.sqrt (1-q) : ℂ) else 0

/-- Literal tensor coordinates of the local records, observing no spatial rail. -/
def environmentRecord : (n : ℕ) → ℝ → HannSpatialQram.Tree n → Environment n → ℂ
  | 0, _, _, _ => 1
  | n + 1, q, t, e => localRecord q t.2.1 e.1 *
      environmentRecord n q t.2.2.1 e.2.1 * environmentRecord n q t.2.2.2 e.2.2

/-- The finite environment inner product, in density-matrix orientation. -/
def recordOverlap (n : ℕ) (q : ℝ) (t u : HannSpatialQram.Tree n) : ℂ :=
  ∑ e : Environment n, environmentRecord n q t e * conj (environmentRecord n q u e)

private theorem local_record_overlap (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (s t : Qutrit) :
    (∑ e : Option Qutrit, localRecord q s e * conj (localRecord q t e)) =
      if s = t then 1 else (q : ℂ) := by
  have h₁ : (Real.sqrt q : ℂ) * (Real.sqrt q : ℂ) = (q : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hq
  have h₂ : (Real.sqrt (1-q) : ℂ) * (Real.sqrt (1-q) : ℂ) = ((1-q : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by linarith : 0 ≤ 1-q)
  cases s <;> cases t <;>
    simp [Fintype.sum_option, localRecord, h₁, h₂]

private theorem record_overlap_step (n : ℕ) (q : ℝ) (t u : HannSpatialQram.Tree (n + 1)) :
    recordOverlap (n + 1) q t u =
      (∑ e : Option Qutrit, localRecord q t.2.1 e * conj (localRecord q u.2.1 e)) *
        recordOverlap n q t.2.2.1 u.2.2.1 * recordOverlap n q t.2.2.2 u.2.2.2 := by
  simp only [recordOverlap, environmentRecord, Fintype.sum_prod_type, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext l; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

private theorem record_overlap_count (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (t u : HannSpatialQram.Tree n) : recordOverlap n q t u = (q : ℂ) ^ routerMismatch n t u := by
  induction n with
  | zero => simp [recordOverlap, environmentRecord, routerMismatch]
  | succ n ih =>
      rw [record_overlap_step, local_record_overlap q hq hq', ih, ih]
      simp only [routerMismatch, pow_add]
      split_ifs <;> simp

/-- The LCP kernel is computed from independent records on the actual loaded routers. -/
private theorem physical_router_kernel (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (a a' : Address n) (b b' : Bool) :
    recordOverlap n q ((load n n) (clean n a b)).2.2
      ((load n n) (clean n a' b')).2.2 =
      if a = a' then 1 else
        (q : ℂ) ^ (2 * (n -
          (D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.lcp
            (addressWord n a) (addressWord n a')).length) - 1) := by
  rw [record_overlap_count n q hq hq', loaded_router_mismatch]
  split_ifs <;> simp



/-- The unchanged gates following the hold: exchange, transport, leaf readout, reverse forward. -/
def postLoad (n : ℕ) (D : Address n → Bool) : Equiv.Perm (State n) :=
  (Equiv.prodCongr (Equiv.refl _) (exchange n)).trans
    ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (transport n))).trans
      ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (readLeaves n D))).trans
        (forward n).symm))

private theorem post_load_clean (n : ℕ) (D : Address n → Bool) (a : Address n) (b : Bool) :
    postLoad n D (load n n (clean n a b)) = clean n a (xor b (D a)) := by
  exact correctness.2.2.1 n D a b

private theorem programmed_injective (n : ℕ) :
    Function.Injective (fun a : Address n => programmed n a n) := by
  induction n with
  | zero => intro a b _; exact Subsingleton.elim _ _
  | succ n ih =>
      intro a b h
      rcases a with ⟨a₀, a⟩
      rcases b with ⟨b₀, b⟩
      cases a₀ <;> cases b₀ <;>
        simp [programmed, encode, Prod.mk.injEq] at h ⊢ <;> exact ih h

private theorem clean_injective (n : ℕ) :
    Function.Injective (fun ab : Address n × Bool => clean n ab.1 ab.2) := by
  intro ab cd h
  have hl := congrArg (load n n) h
  rw [show load n n (clean n ab.1 ab.2) = loading n ab.1 (encode ab.2) n from
    correctness.1 n ab.1 (encode ab.2) n (le_refl n),
    show load n n (clean n cd.1 cd.2) = loading n cd.1 (encode cd.2) n from
    correctness.1 n cd.1 (encode cd.2) n (le_refl n)] at hl
  have ha := programmed_injective n (congrArg (fun s : State n => s.2.2) hl)
  have hb := congrArg (fun s : State n => s.2.1) hl
  change encode ab.2 = encode cd.2 at hb
  have hb' : ab.2 = cd.2 := by
    cases hb₁ : ab.2 <;> cases hb₂ : cd.2 <;> simp_all [encode]
  exact Prod.ext ha hb'

private theorem initialized_clean (n : ℕ) (ψ : Address n × Bool → ℂ)
    (a : Address n) (b : Bool) : initialized n ψ (clean n a b) = ψ (a,b) := by
  have heq (i : Address n) (j : Bool) :
      clean n a b = clean n i j ↔ a = i ∧ b = j := by
    constructor
    · intro h; exact Prod.mk.inj ((clean_injective n) h)
    · rintro ⟨rfl, rfl⟩; rfl
  cases b <;> simp [initialized, heq, eq_comm]

/-- Actual hold marginal after loading, followed by the same system permutation.
The record overlap traces only the independent local environments. -/
def noisyOutput (n : ℕ) (q : ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) : Matrix (State n) (State n) ℂ :=
  fun s t =>
    recordOverlap n q ((postLoad n D).symm s).2.2 ((postLoad n D).symm t).2.2 *
      initialized n ψ ((load n n).symm ((postLoad n D).symm s)) *
      conj (initialized n ψ ((load n n).symm ((postLoad n D).symm t)))

/-- All clean-output matrix entries, for arbitrary complex address/bus amplitudes. -/
private theorem output_matrix_entry (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (D : Address n → Bool) (ψ : Address n × Bool → ℂ)
    (a a' : Address n) (b b' : Bool) :
    noisyOutput n q D ψ (clean n a (xor b (D a))) (clean n a' (xor b' (D a'))) =
      ψ (a,b) * conj (ψ (a',b')) *
        (if a = a' then 1 else (q : ℂ) ^
          (2 * (n - (D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.lcp
            (addressWord n a) (addressWord n a')).length) - 1)) := by
  have hpre (a : Address n) (b : Bool) :
      (postLoad n D).symm (clean n a (xor b (D a))) = load n n (clean n a b) := by
    apply (postLoad n D).injective
    rw [Equiv.apply_symm_apply, post_load_clean]
  simp only [noisyOutput, hpre, Equiv.symm_apply_apply, initialized_clean]
  rw [physical_router_kernel n q hq hq']
  ring

/-- No output matrix entry survives outside the clean-output span. -/
private theorem output_support (n : ℕ) (q : ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) (s t : State n)
    (h : (∀ a b, s ≠ clean n a b) ∨ (∀ a b, t ≠ clean n a b)) :
    noisyOutput n q D ψ s t = 0 := by
  have hz (s : State n) (hs : ∀ a b, s ≠ clean n a b) :
      initialized n ψ ((load n n).symm ((postLoad n D).symm s)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    have hne : (load n n).symm ((postLoad n D).symm s) ≠ clean n a b := by
      intro he
      have he' := congrArg (fun x => postLoad n D (load n n x)) he
      simp only [Equiv.apply_symm_apply, post_load_clean] at he'
      exact hs a (xor b (D a)) he'
    simp [hne]
  rcases h with h | h <;> simp [noisyOutput, hz _ h]




/-- The proposed real tree kernel, independently connected to the physical records above. -/
def kernel (n : ℕ) (q : ℝ) (a a' : Address n) : ℝ :=
  if a = a' then 1 else q ^ (2 * (n -
    (D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.lcp
      (addressWord n a) (addressWord n a')).length) - 1)

/-- The normalized row sum, with the empty depth-zero sum. -/
def minimumFidelity (n : ℕ) (q : ℝ) : ℝ :=
  (1 + ∑ j ∈ Finset.range n, (2 : ℝ)^j * q^(2*j+1)) / (2 : ℝ)^n

/-- The address quadratic form for arbitrary real address weights. -/
def addressEnergy (n : ℕ) (q : ℝ) (p : Address n → ℝ) : ℝ :=
  ∑ a, ∑ a', p a * p a' * kernel n q a a'

private theorem kernel_step (n : ℕ) (q : ℝ) (a a' : Address n) (b c : Bool) :
    kernel (n + 1) q (b,a) (c,a') =
      if b = c then kernel n q a a' else q^(2*n+1) := by
  have hp := (D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.shortest_pop_append
    (addressWord n a) (addressWord n a')).1.1.length_le
  rw [address_word_length] at hp
  have he : 2 * (n + 1) - 1 = 2*n+1 := by omega
  cases b <;> cases c <;>
    simp [kernel, addressWord, D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.lcp,
      Prod.mk.injEq, he, Nat.add_sub_add_right]

private theorem minimum_step (n : ℕ) (q : ℝ) :
    minimumFidelity (n + 1) q = (minimumFidelity n q + q^(2*n+1))/2 := by
  simp only [minimumFidelity, Finset.sum_range_succ, pow_succ]
  field_simp
  ring_nf

private theorem minimum_ge_cross (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1) :
    q^(2*n+1) ≤ minimumFidelity n q := by
  induction n with
  | zero => simpa [minimumFidelity] using hq'
  | succ n ih =>
      rw [minimum_step]
      have hh : q^(2*(n + 1)+1) ≤ q^(2*n+1) :=
        pow_le_pow_of_le_one hq hq' (by omega)
      linarith

private theorem energy_step (n : ℕ) (q : ℝ) (p : Address (n + 1) → ℝ) :
    addressEnergy (n + 1) q p =
      addressEnergy n q (fun a => p (false,a)) +
      addressEnergy n q (fun a => p (true,a)) +
      2 * q^(2*n+1) * (∑ a, p (false,a)) * (∑ a, p (true,a)) := by
  have hc (b c : Bool) :
      (∑ a, ∑ a', p (b,a) * p (c,a') * q^(2*n+1)) =
        q^(2*n+1) * (∑ a, p (b,a)) * (∑ a, p (c,a)) := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
    ring
  simp only [addressEnergy, Fintype.sum_prod_type, Fintype.sum_bool, kernel_step,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Finset.sum_add_distrib]
  rw [hc, hc]
  ring

private theorem energy_lower_bound (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (p : Address n → ℝ) :
    minimumFidelity n q * (∑ a, p a)^2 ≤ addressEnergy n q p := by
  induction n with
  | zero => simp [minimumFidelity, addressEnergy, kernel, pow_two]
  | succ n ih =>
      rw [energy_step, minimum_step]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool]
      have h₀ := ih (fun a => p (false,a))
      have h₁ := ih (fun a => p (true,a))
      have hd := mul_nonneg (sub_nonneg.mpr (minimum_ge_cross n q hq hq'))
        (sq_nonneg ((∑ a, p (false,a)) - ∑ a, p (true,a)))
      nlinarith

private theorem address_card (n : ℕ) : Fintype.card (Address n) = 2^n := by
  induction n with
  | zero => simp [ReversibleQram.Address]
  | succ n ih => simp [ReversibleQram.Address, Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

private theorem kernel_row_sum (n : ℕ) (q : ℝ) (a : Address n) :
    (∑ a', kernel n q a a') = (2 : ℝ)^n * minimumFidelity n q := by
  induction n with
  | zero => simp [kernel, minimumFidelity]
  | succ n ih =>
      rcases a with ⟨b,a⟩
      rw [minimum_step, pow_succ]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, kernel_step]
      have hc : (Fintype.card (Address n) : ℝ) = (2 : ℝ)^n := by
        rw [address_card]; norm_cast
      cases b <;> simp [ih, hc] <;> ring

private theorem uniform_energy (n : ℕ) (q : ℝ) :
    addressEnergy n q (fun _ => ((2 : ℝ)^n)⁻¹) = minimumFidelity n q := by
  have hcard : (Fintype.card (Address n) : ℝ) = (2 : ℝ)^n := by
    rw [address_card]; norm_cast
  simp only [addressEnergy, ← Finset.mul_sum, kernel_row_sum]
  simp [hcard, mul_assoc]



/-- Ideal clean-output basis labelled by input address and bus. -/
def outputBasis (n : ℕ) (D : Address n → Bool) (ab : Address n × Bool) : State n :=
  clean n ab.1 (xor ab.2 (D ab.1))

/-- The ideal initialized output, on the complete physical system basis. -/
def idealOutput (n : ℕ) (D : Address n → Bool) (ψ : Address n × Bool → ℂ) : State n → ℂ :=
  fun s => ∑ ab, if s = outputBasis n D ab then ψ ab else 0

/-- Squared pure-state fidelity, with both sums over the complete physical system. -/
def squaredFidelity (n : ℕ) (q : ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) : ℂ :=
  ∑ s, ∑ t, conj (idealOutput n D ψ s) * noisyOutput n q D ψ s t * idealOutput n D ψ t

/-- Address probabilities retain arbitrary bus amplitudes and correlations. -/
def addressProbability (n : ℕ) (ψ : Address n × Bool → ℂ) (a : Address n) : ℝ :=
  ∑ b, Complex.normSq (ψ (a,b))

private theorem sum_ket {ι σ : Type} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (v : ι → σ) (ψ : ι → ℂ) (g : σ → ℂ) :
    (∑ s, (∑ i, if s = v i then ψ i else 0) * g s) = ∑ i, ψ i * g (v i) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

private theorem sum_ket_conj {ι σ : Type} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (v : ι → σ) (ψ : ι → ℂ) (g : σ → ℂ) :
    (∑ s, conj (∑ i, if s = v i then ψ i else 0) * g s) =
      ∑ i, conj (ψ i) * g (v i) := by
  simp only [map_sum, apply_ite, map_zero]
  exact sum_ket v (fun i => conj (ψ i)) g

private theorem fidelity_formula (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (D : Address n → Bool) (ψ : Address n × Bool → ℂ) :
    squaredFidelity n q D ψ = (addressEnergy n q (addressProbability n ψ) : ℂ) := by
  unfold squaredFidelity idealOutput
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sum_ket_conj]
  simp_rw [mul_comm (noisyOutput n q D ψ _ _), sum_ket, Finset.mul_sum]
  have he (ab cd : Address n × Bool) :
      noisyOutput n q D ψ (outputBasis n D ab) (outputBasis n D cd) =
        ψ ab * conj (ψ cd) * (kernel n q ab.1 cd.1 : ℂ) := by
    simpa only [outputBasis, kernel, apply_ite, Complex.ofReal_one, Complex.ofReal_pow]
      using output_matrix_entry n q hq hq' D ψ ab.1 cd.1 ab.2 cd.2
  simp_rw [he]
  have hm (x y z : ℂ) : conj x * (y * (x * conj y * z)) =
      (Complex.normSq x : ℂ) * (Complex.normSq y : ℂ) * z := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  simp_rw [hm]
  simp only [addressEnergy, addressProbability, Fintype.sum_prod_type,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a' _
  rw [Finset.sum_comm]

/-- The normalized input condition on the complete address/bus amplitudes. -/
def Normalized (n : ℕ) (ψ : Address n × Bool → ℂ) : Prop :=
  ∑ ab, Complex.normSq (ψ ab) = 1

private theorem output_basis_injective (n : ℕ) (D : Address n → Bool) :
    Function.Injective (outputBasis n D) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have he : (a, xor b (D a)) = (c, xor d (D c)) := clean_injective n h
  obtain ⟨ha,hb⟩ := Prod.mk.inj he
  subst c
  have hbd : b = d := by
    cases b <;> cases d <;> cases hd : D a <;> simp_all
  exact congrArg (fun bb => (a,bb)) hbd

private theorem ideal_at_basis (n : ℕ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) (ab : Address n × Bool) :
    idealOutput n D ψ (outputBasis n D ab) = ψ ab := by
  simp only [idealOutput, (output_basis_injective n D).eq_iff]
  simp

private theorem ideal_normalized (n : ℕ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) (hψ : Normalized n ψ) :
    ∑ s, Complex.normSq (idealOutput n D ψ s) = 1 := by
  have hh := sum_ket (outputBasis n D) ψ (fun s => conj (idealOutput n D ψ s))
  change (∑ s, idealOutput n D ψ s * conj (idealOutput n D ψ s)) = _ at hh
  simp only [Complex.mul_conj, ideal_at_basis] at hh
  have hhr : (∑ s, Complex.normSq (idealOutput n D ψ s)) =
      ∑ ab, Complex.normSq (ψ ab) := by exact_mod_cast hh
  exact hhr.trans hψ

/-- The uniform-address input with bus false; its amplitude is the positive inverse square root. -/
def uniformInput (n : ℕ) : Address n × Bool → ℂ :=
  fun ab => if ab.2 then 0 else ((Real.sqrt ((2 : ℝ)^n))⁻¹ : ℝ)

private theorem uniform_prob (n : ℕ) (a : Address n) :
    addressProbability n (uniformInput n) a = ((2 : ℝ)^n)⁻¹ := by
  have hp : 0 < (2 : ℝ)^n := by positivity
  simp [addressProbability, uniformInput, Complex.normSq_ofReal]

private theorem uniform_amplitude (n : ℕ) :
    (Real.sqrt ((2 : ℝ)^n))⁻¹ = (2 : ℝ)^(-(n : ℝ)/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

private theorem uniform_normalized (n : ℕ) : Normalized n (uniformInput n) := by
  have hc : (Fintype.card (Address n) : ℝ) = (2 : ℝ)^n := by
    rw [address_card]; norm_cast
  change (∑ ab, Complex.normSq (uniformInput n ab)) = 1
  rw [Fintype.sum_prod_type]
  change (∑ a, addressProbability n (uniformInput n) a) = 1
  simp [uniform_prob, hc]



/-- The actual joint output before tracing the independent router environments. -/
def jointOutput (n : ℕ) (q : ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) (s : State n) (e : Environment n) : ℂ :=
  initialized n ψ ((load n n).symm ((postLoad n D).symm s)) *
    environmentRecord n q ((postLoad n D).symm s).2.2 e

private theorem output_partial_trace (n : ℕ) (q : ℝ) (D : Address n → Bool)
    (ψ : Address n × Bool → ℂ) (s t : State n) :
    (∑ e, jointOutput n q D ψ s e * conj (jointOutput n q D ψ t e)) =
      noisyOutput n q D ψ s t := by
  simp only [jointOutput, noisyOutput, recordOverlap, map_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- One hold on every actual internal router, its complete output, exact fidelity and sharp minimum. -/
theorem result (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1) (D : Address n → Bool) :
    (∀ (X : Matrix Qutrit Qutrit ℂ) (s t : Qutrit),
      (∑ e, localRecord q s e * conj (localRecord q t e)) * X s t =
        (q : ℂ) * X s t + (1-(q : ℂ)) * (if s = t then X s t else 0)) ∧
    (∀ t : HannSpatialQram.Tree n, recordOverlap n q t t = 1) ∧
    (∀ (a a' : Address n) (b b' : Bool),
      routerMismatch n ((load n n) (clean n a b)).2.2
        ((load n n) (clean n a' b')).2.2 =
          (if a = a' then 0 else 2 * (n -
            (D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry.lcp
              (addressWord n a) (addressWord n a')).length) - 1) ∧
      recordOverlap n q ((load n n) (clean n a b)).2.2
        ((load n n) (clean n a' b')).2.2 = (kernel n q a a' : ℂ)) ∧
    (∀ (ψ : Address n × Bool → ℂ) (s t : State n),
      (∑ e, jointOutput n q D ψ s e * conj (jointOutput n q D ψ t e)) =
        noisyOutput n q D ψ s t) ∧
    (∀ (ψ : Address n × Bool → ℂ) (a a' : Address n) (b b' : Bool),
      noisyOutput n q D ψ (clean n a (xor b (D a))) (clean n a' (xor b' (D a'))) =
        ψ (a,b) * conj (ψ (a',b')) * (kernel n q a a' : ℂ)) ∧
    (∀ (ψ : Address n × Bool → ℂ) (s t : State n),
      ((∀ a b, s ≠ clean n a b) ∨ (∀ a b, t ≠ clean n a b)) →
        noisyOutput n q D ψ s t = 0) ∧
    (∀ ψ : Address n × Bool → ℂ, Normalized n ψ →
      (∑ s, Complex.normSq (idealOutput n D ψ s)) = 1 ∧
      squaredFidelity n q D ψ = (addressEnergy n q (addressProbability n ψ) : ℂ) ∧
        minimumFidelity n q ≤ (squaredFidelity n q D ψ).re) ∧
    Normalized n (uniformInput n) ∧
      squaredFidelity n q D (uniformInput n) = (minimumFidelity n q : ℂ) ∧
      minimumFidelity 0 q = 1 ∧
      (∀ ab, uniformInput n ab = if ab.2 then 0 else
        (((2 : ℝ)^(-(n : ℝ)/2) : ℝ) : ℂ)) := by
  refine ⟨?_, ?_, ?_, output_partial_trace n q D, ?_, output_support n q D, ?_,
    uniform_normalized n, ?_, ?_, ?_⟩
  · intro X s t
    rw [local_record_overlap q hq hq']
    split_ifs <;> ring
  · intro t
    rw [record_overlap_count n q hq hq', router_mismatch_self, pow_zero]
  · intro a a' b b'
    refine ⟨loaded_router_mismatch n a a' b b', ?_⟩
    simpa only [kernel, apply_ite, Complex.ofReal_one, Complex.ofReal_pow]
      using physical_router_kernel n q hq hq' a a' b b'
  · intro ψ a a' b b'
    simpa only [kernel, apply_ite, Complex.ofReal_one, Complex.ofReal_pow]
      using output_matrix_entry n q hq hq' D ψ a a' b b'
  · intro ψ hψ
    refine ⟨ideal_normalized n D ψ hψ, fidelity_formula n q hq hq' D ψ, ?_⟩
    rw [fidelity_formula n q hq hq' D ψ, Complex.ofReal_re]
    have hm : (∑ a, addressProbability n ψ a) = 1 := by
      exact (Fintype.sum_prod_type _).symm.trans hψ
    simpa only [hm, one_pow, mul_one] using
      energy_lower_bound n q hq hq' (addressProbability n ψ)
  · rw [fidelity_formula n q hq hq' D, show addressProbability n (uniformInput n) =
        (fun _ => ((2 : ℝ)^n)⁻¹) from funext (uniform_prob n), uniform_energy]
  · simp [minimumFidelity]
  · intro ab
    simp only [uniformInput, uniform_amplitude]

#print axioms result

end D5.S3.Quantum.Routing.HannRouterDephasing
