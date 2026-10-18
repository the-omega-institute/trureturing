/- GID: D5/S3/Quantum/Entanglement/SequentialOccupationHistory
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SequentialOccupationHistory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Occupation transitions give isometries and exact word contraction. -/

import D5.S3.Quantum.Entanglement.CoherentHistorySchmidt
import D5.S3.Quantum.Foundation.FiniteKrausChannel

/- The actual contraction and cut-factorization constructions use varying bond
carriers. Active nextStep maps are isometries, but no unitary circuit on one fixed
memory register is constructed here. The general chain foundation and transported
5040 specialization therefore do not close the complete coherent-history atom. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.SequentialOccupationHistory

noncomputable section
open scoped BigOperators
open OccupancyWordSectors CoherentHistorySchmidt

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
private theorem extension_le_iff {a b : Multiset α} (hb : b ≤ a) (i : α) :
    b + {i} ≤ a ↔ b.count i < a.count i := by
  constructor
  · intro h
    have hc := Multiset.count_le_of_le i h
    simpa using hc
  · intro hi
    apply Multiset.le_iff_count.mpr
    intro j
    by_cases hj : j = i
    · subst j
      simpa using hi
    · simpa [hj] using Multiset.count_le_of_le j hb

omit [Fintype α] in
theorem extension_exists_iff {a : Multiset α} {t : ℕ} (b : Boundary a t) (i : α) :
    (∃ c : Boundary a (t + 1), c.val = b.val + {i}) ↔ b.val.count i < a.count i := by
  constructor
  · rintro ⟨c, hc⟩
    exact (extension_le_iff (boundary_spec a t b).1 i).mp
      (hc ▸ (boundary_spec a (t + 1) c).1)
  · intro hi
    refine ⟨⟨b.val + {i}, ?_⟩, rfl⟩
    have hl := (extension_le_iff (boundary_spec a t b).1 i).mpr hi
    simp [boundaries, Multiset.mem_powersetCard, hl, (boundary_spec a t b).2]

def nextStep (a : Multiset α) (t : ℕ) :
    Matrix (α × Boundary a (t + 1)) (Boundary a t) ℂ :=
  fun p b => if p.2.val = b.val + {p.1} then
    (Real.sqrt (((a - b.val).count p.1 : ℝ) / (a.card - t : ℕ)) : ℂ) else 0

omit [Fintype α] in
private theorem next_step_column_norm (a : Multiset α) (t : ℕ)
    (b : Boundary a t) (i : α) :
    (∑ c : Boundary a (t + 1), star (nextStep a t (i, c) b) * nextStep a t (i, c) b) =
      (((a - b.val).count i : ℝ) / (a.card - t : ℕ) : ℂ) := by
  classical
  by_cases hi : b.val.count i < a.count i
  · obtain ⟨c, hc⟩ := (extension_exists_iff b i).mpr hi
    rw [Finset.sum_eq_single c]
    · simp only [nextStep, hc, if_pos, Complex.star_def, Complex.conj_ofReal]
      norm_cast
      exact Real.mul_self_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · intro d _ hdc
      have hd : d.val ≠ b.val + {i} := fun hd => hdc (Subtype.ext (hd.trans hc.symm))
      simp [nextStep, hd]
    · simp
  · have hz : (a - b.val).count i = 0 := by
      rw [Multiset.count_sub]
      omega
    have hn (c : Boundary a (t + 1)) : c.val ≠ b.val + {i} :=
      fun hc => hi ((extension_exists_iff b i).mp ⟨c, hc⟩)
    simp [nextStep, hn, hz]

theorem next_step_gram {a : Multiset α} {t : ℕ} (ht : t < a.card) :
    (nextStep a t).conjTranspose * nextStep a t = 1 := by
  classical
  ext b d
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, Matrix.one_apply]
  by_cases hbd : b = d
  · subst d
    rw [if_pos rfl]
    simp_rw [next_step_column_norm]
    have hs : (∑ i : α, (a - b.val).count i) = a.card - t := by
      rw [Multiset.sum_count_eq_card (fun _ _ => Finset.mem_univ _),
        Multiset.card_sub (boundary_spec a t b).1, (boundary_spec a t b).2]
    have hn : ((a.card - t : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt ht).ne'
    push_cast
    rw [← Finset.sum_div, ← Nat.cast_sum, hs, div_self hn]
  · rw [if_neg hbd]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro c _
    have hn : ¬ (c.val = b.val + {i} ∧ c.val = d.val + {i}) := by
      rintro ⟨hb, hd⟩
      exact hbd (Subtype.ext (add_right_cancel (hb.symm.trans hd)))
    by_cases hb : c.val = b.val + {i}
    · have hd : c.val ≠ d.val + {i} := fun hd => hn ⟨hb, hd⟩
      simp only [nextStep, if_pos hb, if_neg hd, mul_zero]
    · simp [nextStep, hb]

theorem next_step_quantum_channel {a : Multiset α} {t : ℕ} (ht : t < a.card) :
    ∃ channel : D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel
        (Boundary a t) (α × Boundary a (t + 1)),
      ∀ rho : Matrix (Boundary a t) (Boundary a t) ℂ,
        CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
        nextStep a t * rho * (nextStep a t).conjTranspose := by
  classical
  simpa using D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
    (fun _ : Unit => nextStep a t) (by simpa using next_step_gram ht)

private theorem conditional_amplitude {r : Multiset α} {n : ℕ}
    (h : r.card = n + 1) (i : α) (hi : i ∈ r) :
    (Real.sqrt ((r.count i : ℝ) / (n + 1 : ℕ)) : ℂ) *
        historyAmplitude (r.erase i) n = historyAmplitude r (n + 1) := by
  have he : (r.erase i).card = n := by
    rw [Multiset.card_erase_of_mem hi, h]; rfl
  have hm : (multiplicity (n + 1) r : ℝ) ≠ 0 := by
    exact_mod_cast (multiplicity_pos r h).ne'
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hr : (r.count i : ℝ) / (n + 1 : ℕ) =
      (multiplicity n (r.erase i) : ℝ) / multiplicity (n + 1) r := by
    apply (div_eq_div_iff hn hm).mpr
    have hc := multiplicity_erase_mul h i hi
    exact_mod_cast (by nlinarith [hc] : r.count i * multiplicity (n + 1) r =
      multiplicity n (r.erase i) * (n + 1))
  have hs : (Real.sqrt (multiplicity n (r.erase i) : ℝ) : ℂ) ≠ 0 := by
    have hp : (0 : ℝ) < multiplicity n (r.erase i) := by
      exact_mod_cast multiplicity_pos (r.erase i) he
    exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
  rw [hr, Real.sqrt_div (Nat.cast_nonneg _)]
  simp only [historyAmplitude, Complex.ofReal_div]
  field_simp

theorem sector_head {r : Multiset α} {n : ℕ} (h : r.card = n + 1)
    (w : Word α (n + 1)) :
    sectorVector (n + 1) r w = if w 0 ∈ r then
      (Real.sqrt ((r.count (w 0) : ℝ) / (n + 1 : ℕ)) : ℂ) *
        sectorVector n (r.erase (w 0)) (Fin.tail w) else 0 := by
  have hw : occupation w = w 0 ::ₘ occupation (Fin.tail w) := by
    conv_lhs => rw [← Fin.cons_self_tail w]
    simp only [occupation, List.ofFn_cons]; rfl
  have hl : occupation w = r ↔ w 0 ∈ r ∧ occupation (Fin.tail w) = r.erase (w 0) := by
    rw [hw, ← Multiset.singleton_add, add_comm ({w 0} : Multiset α),
      Multiset.add_singleton_eq_iff]
  by_cases hi : w 0 ∈ r
  · by_cases ht : occupation (Fin.tail w) = r.erase (w 0)
    · have hf := hl.mpr ⟨hi, ht⟩
      simpa [sectorVector, sectorWords, hi, ht, hf, historyAmplitude] using
        (conditional_amplitude h (w 0) hi).symm
    · have hf : occupation w ≠ r := fun hf => ht (hl.mp hf).2
      simp [sectorVector, sectorWords, hi, ht, hf]
  · have hf : occupation w ≠ r := fun hf => hi (hl.mp hf).1
    simp [sectorVector, sectorWords, hi, hf]

/-- Contract the actual step entries, capped by the terminal occupation basis vector. -/
def contraction (a : Multiset α) : (n t : ℕ) → Word α n → Boundary a t → ℂ
  | 0, _, _, b => if b.val = a then 1 else 0
  | n + 1, t, w, b => ∑ c : Boundary a (t + 1),
      nextStep a t (w 0, c) b * contraction a n (t + 1) (Fin.tail w) c

theorem contraction_eq_sector (a : Multiset α) (n t : ℕ) (h : a.card = t + n)
    (w : Word α n) (b : Boundary a t) :
    contraction a n t w b = sectorVector n (a - b.val) w := by
  induction n generalizing t with
  | zero =>
    have hr : a - b.val = 0 := Multiset.card_eq_zero.mp (complement_card h b)
    have hb : b.val = a := by
      simpa [hr] using Multiset.sub_add_cancel (boundary_spec a t b).1
    have hw : w = default := Subsingleton.elim _ _
    simp [contraction, hb, sectorVector, sectorWords, occupation,
      OccupancyWordSectors.multiplicity, hw]
  | succ n ih =>
    have hr : (a - b.val).card = n + 1 := complement_card h b
    rw [sector_head hr]
    by_cases hi : w 0 ∈ a - b.val
    · obtain ⟨c, hc⟩ := (extension_exists_iff b (w 0)).mpr (Multiset.mem_sub.mp hi)
      have hcres : a - c.val = (a - b.val).erase (w 0) := by
        rw [hc, Multiset.sub_add_eq_sub_sub, Multiset.sub_singleton]
      rw [if_pos hi, contraction, Finset.sum_eq_single c]
      · rw [ih (t + 1) (by omega), hcres]
        have hn : a.card - t = n + 1 := by omega
        simp only [nextStep, hc, if_true, hn]
      · intro d _ hdc
        have hd : d.val ≠ b.val + {w 0} := fun hd => hdc (Subtype.ext (hd.trans hc.symm))
        simp only [nextStep, if_neg hd, zero_mul]
      · simp
    · rw [if_neg hi, contraction]
      apply Finset.sum_eq_zero
      intro c _
      have hc : c.val ≠ b.val + {w 0} := fun hc =>
        hi (Multiset.mem_sub.mpr ((extension_exists_iff b (w 0)).mp ⟨c, hc⟩))
      simp only [nextStep, if_neg hc, zero_mul]

def initialBoundary (a : Multiset α) : Boundary a 0 :=
  ⟨0, by simp [boundaries]⟩

theorem history_sequential_preparation (a : Multiset α) (w : Word α a.card) :
    contraction a a.card 0 w (initialBoundary a) = sectorVector a.card a w := by
  simpa [initialBoundary] using contraction_eq_sector a a.card 0 (by omega) w
    (initialBoundary a)

theorem coefficient_rank_le_bond {β : Type*} [Fintype β]
    (a : Multiset α) (t s : ℕ) (P : Matrix (Word α t) β ℂ)
    (Q : Matrix β (Word α s) ℂ) (h : coefficientMatrix a t s = P * Q) :
    (coefficientMatrix a t s).rank ≤ Fintype.card β := by
  rw [h]
  exact (Matrix.rank_mul_le_left P Q).trans (Matrix.rank_le_card_width P)

universe u v

/-- A finite rectangular chain; each constructor stores its actual next bond. -/
inductive FiniteChain (α : Type v) : Type u → Type (max v (u + 1))
  | terminal {β : Type u} (cap : β → ℂ) : FiniteChain α β
  | step {β γ : Type u} [finite : Fintype γ] (transition : α → Matrix β γ ℂ)
      (rest : FiniteChain α γ) : FiniteChain α β

namespace FiniteChain

variable {A : Type v} {B : Type u}

def length : {B : Type u} → FiniteChain A B → ℕ
  | _, .terminal _ => 0
  | _, .step (finite := _) _ rest => rest.length + 1

/-- The total definition is used only at cuts not exceeding length. -/
def cutBond {B : Type u} (c : FiniteChain A B) (t : ℕ) : Type u :=
  match t, c with
  | 0, _ => B
  | _ + 1, .terminal _ => B
  | t + 1, .step (finite := _) _ rest => rest.cutBond t
termination_by structural t

instance cutFintype {B : Type u} [finite : Fintype B]
    (c : FiniteChain A B) (t : ℕ) : Fintype (c.cutBond t) :=
  match t, c with
  | 0, _ => finite
  | _ + 1, .terminal _ => finite
  | t + 1, .step (finite := _) _ rest => rest.cutFintype t
termination_by structural t

/-- Actual finite sums of products, with zero on incompatible word lengths. -/
def contract : {B : Type u} → FiniteChain A B → List A → B → ℂ
  | _, .terminal cap, [], i => cap i
  | _, .terminal _, _ :: _, _ => 0
  | _, .step (finite := _) _ _, [], _ => 0
  | _, .step (finite := _) transition rest, x :: xs, i =>
      ∑ j, transition x i j * rest.contract xs j

def left : {B : Type u} → (c : FiniteChain A B) → (t : ℕ) →
    List A → B → c.cutBond t → ℂ
  | _, _, 0, _, i, b => by classical exact if i = b then 1 else 0
  | _, .terminal _, _ + 1, _, _, _ => 0
  | _, .step (finite := _) _ _, _ + 1, [], _, _ => 0
  | _, .step (finite := _) transition rest, t + 1, x :: xs, i, b =>
      ∑ j, transition x i j * rest.left t xs j b

def right : {B : Type u} → (c : FiniteChain A B) → (t : ℕ) →
    List A → c.cutBond t → ℂ
  | _, c, 0, v, b => c.contract v b
  | _, .terminal _, _ + 1, _, _ => 0
  | _, .step (finite := _) _ rest, t + 1, v, b => rest.right t v b

def amplitude [Fintype B] (c : FiniteChain A B) (initial : B → ℂ)
    {n : ℕ} (w : Word A n) : ℂ := ∑ i, initial i * c.contract (List.ofFn w) i

def prefixMatrix [Fintype B] (c : FiniteChain A B) (initial : B → ℂ) (t : ℕ) :
    Matrix (Word A t) (c.cutBond t) ℂ :=
  fun u b => ∑ i, initial i * c.left t (List.ofFn u) i b

def suffixMatrix (c : FiniteChain A B) (t s : ℕ) :
    Matrix (c.cutBond t) (Word A s) ℂ := fun b v => c.right t (List.ofFn v) b

/-- Maximum of the actual bond cardinalities over all legal cuts, endpoints included. -/
def maximumBond [Fintype B] (c : FiniteChain A B) : ℕ :=
  (Finset.range (c.length + 1)).sup (fun t => Fintype.card (c.cutBond t))

end FiniteChain

theorem chain_contract_append {A : Type v} {B : Type u} [Fintype B]
    (c : FiniteChain A B) (t : ℕ) (ht : t ≤ c.length)
    (u v : List A) (hu : u.length = t) (i : B) :
    c.contract (u ++ v) i = ∑ b : c.cutBond t, c.left t u i b * c.right t v b := by
  classical
  induction t generalizing B u with
  | zero =>
    have he : u = [] := List.length_eq_zero_iff.mp hu
    subst u
    cases c <;> simp only [List.nil_append, FiniteChain.left, FiniteChain.right,
      FiniteChain.cutBond, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq] <;>
      exact (if_pos (Finset.mem_univ i)).symm
  | succ t ih =>
    cases c with
    | terminal cap => simp [FiniteChain.length] at ht
    | step transition rest =>
      cases u with
      | nil => simp at hu
      | cons x xs =>
        have ht' : t ≤ rest.length := by simpa [FiniteChain.length] using ht
        have hu' : xs.length = t := by simpa using hu
        simp only [List.cons_append, FiniteChain.contract, FiniteChain.left,
          FiniteChain.right, FiniteChain.cutBond]
        simp_rw [ih rest ht' xs hu', Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm

theorem chain_amplitude_append {A : Type v} {B : Type u} [Fintype B]
    (c : FiniteChain A B) (initial : B → ℂ) (t s : ℕ) (ht : t ≤ c.length)
    (u : Word A t) (v : Word A s) :
    c.amplitude initial (Fin.append u v) =
      (c.prefixMatrix initial t * c.suffixMatrix t s) u v := by
  classical
  simp only [FiniteChain.amplitude, List.ofFn_fin_append, Matrix.mul_apply,
    FiniteChain.prefixMatrix, FiniteChain.suffixMatrix]
  simp_rw [chain_contract_append c t ht _ _ (List.length_ofFn) _,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Exactness identifies the output only; the cut factorization is derived. -/
theorem sequential_coefficient_factorization {B : Type u} [Fintype B]
    (c : FiniteChain α B) (initial : B → ℂ) (a : Multiset α) (t s : ℕ)
    (hlen : c.length = t + s)
    (hexact : ∀ w : Word α (t + s), c.amplitude initial w = sectorVector (t + s) a w) :
    coefficientMatrix a t s = c.prefixMatrix initial t * c.suffixMatrix t s := by
  ext u v
  rw [coefficient_eq_uniform_word, ← hexact]
  exact chain_amplitude_append c initial t s (by omega) u v

theorem sequential_rank_necessity {B : Type u} [Fintype B]
    (c : FiniteChain α B) (initial : B → ℂ) (a : Multiset α) (t s : ℕ)
    (hlen : c.length = t + s)
    (hexact : ∀ w : Word α (t + s), c.amplitude initial w = sectorVector (t + s) a w) :
    (coefficientMatrix a t s).rank ≤ Fintype.card (c.cutBond t) :=
  coefficient_rank_le_bond a t s _ _
    (sequential_coefficient_factorization c initial a t s hlen hexact)

theorem sequential_memory_necessity {B : Type u} [Fintype B]
    (c : FiniteChain α B) (initial : B → ℂ) (a : Multiset α) (t s : ℕ)
    (ha : a.card = t + s) (hlen : c.length = t + s)
    (hexact : ∀ w : Word α (t + s), c.amplitude initial w = sectorVector (t + s) a w) :
    (boundaries a t).card ≤ Fintype.card (c.cutBond t) := by
  rw [← coefficient_rank ha]
  exact sequential_rank_necessity c initial a t s hlen hexact

def occupationChain (a : Multiset α) : (n t : ℕ) → FiniteChain α (Boundary a t)
  | 0, _ => .terminal (fun b => if b.val = a then 1 else 0)
  | n + 1, t => .step (fun i b c => nextStep a t (i, c) b) (occupationChain a n (t + 1))

omit [Fintype α] in
theorem occupation_chain_length (a : Multiset α) (n t : ℕ) :
    (occupationChain a n t).length = n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simpa [occupationChain, FiniteChain.length] using congrArg Nat.succ (ih (t + 1))

omit [Fintype α] in
theorem occupation_chain_bond_card (a : Multiset α) (n t k : ℕ) (hk : k ≤ n) :
    Fintype.card ((occupationChain a n t).cutBond k) = (boundaries a (t + k)).card := by
  induction k generalizing n t with
  | zero => exact Fintype.card_coe _
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      calc
        _ = Fintype.card ((occupationChain a n (t + 1)).cutBond k) :=
          Fintype.card_congr (Equiv.refl _)
        _ = (boundaries a (t + 1 + k)).card := ih n (t + 1) (by omega)
        _ = _ := by rw [show t + 1 + k = t + (k + 1) by omega]

omit [Fintype α] in
theorem occupation_chain_contract (a : Multiset α) (n t : ℕ)
    (w : Word α n) (b : Boundary a t) :
    (occupationChain a n t).contract (List.ofFn w) b = contraction a n t w b := by
  induction n generalizing t with
  | zero => simp [occupationChain, FiniteChain.contract, contraction]
  | succ n ih =>
    have hw : List.ofFn w = w 0 :: List.ofFn (Fin.tail w) := by
      conv_lhs => rw [← Fin.cons_self_tail w]
      exact List.ofFn_cons _ _
    simp only [occupationChain, hw, FiniteChain.contract, contraction]
    simp_rw [ih]

def occupationInitial (a : Multiset α) : Boundary a 0 → ℂ :=
  fun b => if b = initialBoundary a then 1 else 0

theorem occupation_chain_preparation (a : Multiset α) (w : Word α a.card) :
    (occupationChain a a.card 0).amplitude (occupationInitial a) w =
      sectorVector a.card a w := by
  classical
  simp only [FiniteChain.amplitude, occupationInitial, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, occupation_chain_contract]
  exact history_sequential_preparation a w

/-- Algebraic necessity allows arbitrary complex caps and local transitions. -/
theorem maximum_bond_necessity {B : Type u} [Fintype B]
    (c : FiniteChain α B) (initial : B → ℂ) (a : Multiset α)
    (hlen : c.length = a.card)
    (hexact : ∀ w : Word α a.card, c.amplitude initial w = sectorVector a.card a w) :
    boundaryMaximum a ≤ c.maximumBond := by
  apply Finset.sup_le
  intro t ht
  have hs : a.card = t + (a.card - t) := by have := Finset.mem_range.mp ht; omega
  have he : ∀ w : Word α (t + (a.card - t)),
      c.amplitude initial w = sectorVector (t + (a.card - t)) a w := by
    rw [← hs]
    exact hexact
  exact (sequential_memory_necessity c initial a t (a.card - t) hs (hlen.trans hs) he).trans
    (Finset.le_sup (s := Finset.range (c.length + 1))
      (f := fun k => Fintype.card (c.cutBond k)) (by simpa only [hlen] using ht))

omit [Fintype α] in
theorem occupation_chain_maximum_bond (a : Multiset α) :
    (occupationChain a a.card 0).maximumBond = boundaryMaximum a := by
  apply Finset.sup_congr (by rw [occupation_chain_length])
  intro t ht
  simpa using occupation_chain_bond_card a a.card 0 t
    (by have := Finset.mem_range.mp ht; omega)

/-- Achieved values, with the entire exact preparation included in each witness. -/
def achievableMaximumBonds {A : Type u} [Fintype A] [DecidableEq A]
    (a : Multiset A) : Set ℕ :=
  {m | ∃ (B : Type u) (_ : Fintype B) (c : FiniteChain A B) (initial : B → ℂ),
    c.length = a.card ∧
    (∀ w : Word A a.card, c.amplitude initial w = sectorVector a.card a w) ∧
    c.maximumBond = m}

/-- An attained minimum, witnessed by the actual recursively contracted occupation chain. -/
theorem minimum_maximum_bond_characterization (a : Multiset α) :
    IsLeast (achievableMaximumBonds a) (boundaryMaximum a) := by
  constructor
  · exact ⟨Boundary a 0, inferInstance, occupationChain a a.card 0, occupationInitial a,
      occupation_chain_length a a.card 0, occupation_chain_preparation a,
      occupation_chain_maximum_bond a⟩
  · rintro m ⟨B, hB, c, initial, hlen, hexact, hm⟩
    let _ := hB
    rw [← hm]
    exact maximum_bond_necessity c initial a hlen hexact

theorem history_5040_minimum_maximum_bond :
    IsLeast (achievableMaximumBonds occupation5040) 12 := by
  rw [← occupation_5040_boundary_maximum]
  exact minimum_maximum_bond_characterization occupation5040

theorem history_5040_occupation_chain_attainment :
    (occupationChain occupation5040 occupation5040.card 0).length = 8 ∧
    (occupationChain occupation5040 occupation5040.card 0).maximumBond = 12 ∧
    ∀ w : Word (Option (Fin 3)) occupation5040.card,
      (occupationChain occupation5040 occupation5040.card 0).amplitude
        (occupationInitial occupation5040) w =
          sectorVector occupation5040.card occupation5040 w := by
  exact ⟨(occupation_chain_length _ _ _).trans occupation_5040_card,
    (occupation_chain_maximum_bond _).trans occupation_5040_boundary_maximum,
    occupation_chain_preparation _⟩

example : IsLeast (achievableMaximumBonds (0 : Multiset (Fin 0))) 1 := by
  simpa [boundaryMaximum, boundaries] using
    minimum_maximum_bond_characterization (0 : Multiset (Fin 0))

example (a : Multiset α) : Fintype.card (Boundary a 0) = 1 ∧
    Fintype.card ((occupationChain a a.card 0).cutBond a.card) = 1 := by
  rw [occupation_chain_bond_card a a.card 0 a.card le_rfl]
  simp [boundaries]

example {B : Type u} [Fintype B] (c : FiniteChain (Option (Fin 3)) B) (initial : B → ℂ)
    (hlen : c.length = 8)
    (hexact : ∀ w : Word (Option (Fin 3)) 8,
      c.amplitude initial w = sectorVector 8 occupation5040 w) : 12 ≤ c.maximumBond := by
  rw [← occupation_5040_boundary_maximum]
  apply maximum_bond_necessity c initial occupation5040 (hlen.trans occupation_5040_card.symm)
  rw [occupation_5040_card]
  exact hexact

example : 12 ∈ achievableMaximumBonds occupation5040 :=
  history_5040_minimum_maximum_bond.1

example (w : Word (Fin 0) 0) :
    (occupationChain (0 : Multiset (Fin 0)) 0 0).amplitude (occupationInitial 0) w =
      sectorVector 0 0 w := occupation_chain_preparation 0 w

end
end D5.S3.Quantum.Entanglement.SequentialOccupationHistory
