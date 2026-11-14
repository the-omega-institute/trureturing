/- GID: D5/S3/Quantum/Routing/HannRouterDephasing
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannRouterDephasing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual loaded router mismatch counts and single-hold dephasing. -/


import D5.S3.Quantum.Routing.HannSpatialQram
import D5.S3.Combinatorics.Graph.Walks.BinaryWordGeometry

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
    recordOverlap (n+1) q t u =
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
theorem physical_router_kernel (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
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
theorem output_matrix_entry (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1)
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
theorem output_support (n : ℕ) (q : ℝ) (D : Address n → Bool)
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

#print axioms output_matrix_entry
#print axioms output_support

end D5.S3.Quantum.Routing.HannRouterDephasing
