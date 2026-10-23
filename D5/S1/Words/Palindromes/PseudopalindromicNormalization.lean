/- GID: D5/S1/Words/Palindromes/PseudopalindromicNormalization
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PseudopalindromicNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Generalized pseudostandard words and involutory reflection structure. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15921
  audit targets include finite_border_period and pre_prefix.
Fixed-point equations and finite prefixes reuse Function.IsFixedPt and List.ofFn.
The letter equivalence uses Function.Involutive.toPerm.
Content witness: period_extend_left; its strong-induction chain supplies normalization.
Declaration: InvAntimorphism; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.border_periodic
Declaration: InvAntimorphism.map_nil; proof_shape: bind-only; escape_witness: none
  consumer: InvAntimorphism.map_eq_nil_iff, two_letter_pal, closure_bounds
Declaration: InvAntimorphism.map_eq_nil_iff; proof_shape: bind-only; escape_witness: none
  consumer: InvAntimorphism.length_lower
Declaration: InvAntimorphism.length_lower; proof_shape: bind-only; escape_witness: none
  consumer: InvAntimorphism.length_map
Declaration: InvAntimorphism.length_map; proof_shape: bind-only; escape_witness: none
  consumer: InvAntimorphism.singletonExists
Declaration: InvAntimorphism.singletonExists; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.gap_bound
Declaration: InvAntimorphism.letter; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.gap_bound
Declaration: InvAntimorphism.map_singleton; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.tail_necessary
Declaration: InvAntimorphism.letterInvolutive; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.InvAntimorphism.perm_square
Declaration: InvAntimorphism.perm; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.border_periodic
Declaration: InvAntimorphism.perm_apply; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.gap_bound
Declaration: InvAntimorphism.perm_unique; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.fromInvolution_perm
Declaration: InvAntimorphism.representation; proof_shape: bind-only; escape_witness: none
  conclusion: a permutation with the reversed-letter representation; consumer: InvAntimorphism.map_word
Declaration: InvAntimorphism.map_word; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.gap_bound
Declaration: two_letter_pal; proof_shape: bind-only; escape_witness: none
  consumer: palindrome_transport_iff
Declaration: palindrome_transport_iff; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.tail_necessary
Declaration: InvAntimorphism.prefix_to_suffix; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.gap_bound
Declaration: IsClosure; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.border_periodic
Declaration: Generates; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.border_periodic
Declaration: InvAntimorphism.extension_tail; proof_shape: bind-only; escape_witness: none
  consumer: InvAntimorphism.extension_overlap
Declaration: InvAntimorphism.extension_overlap; proof_shape: bind-only; escape_witness: none
  consumer: closure_prefix
Declaration: cut; proof_shape: bind-only; escape_witness: none
  consumer: closure
Declaration: cut_spec; proof_shape: bind-only; escape_witness: none
  consumer: closure_pal, closure_prefix
Declaration: cut_min; proof_shape: bind-only; escape_witness: none
  consumer: cut_le_length, closure_spec
Declaration: cut_le_length; proof_shape: bind-only; escape_witness: none
  consumer: closure_length, closure_spec
Declaration: closure; proof_shape: bind-only; escape_witness: none
  consumer: closure_pal, closure_length, closure_spec, earliest_insertion
Declaration: closure_pal; proof_shape: bind-only; escape_witness: none
  consumer: closure_spec
Declaration: closure_length; proof_shape: bind-only; escape_witness: none
  consumer: closure_spec
Declaration: closure_spec; proof_shape: bind-only; escape_witness: none
  consumer: earliest_insertion
Declaration: closure_bounds; proof_shape: bind-only; escape_witness: none
  conclusion: the upper bound z.length ≤ 2 * w.length; consumer: closure_prefix
Declaration: pal_wrap; proof_shape: bind-only; escape_witness: none
  consumer: two_letter_pal, closure_pal, closure_suffix_bound, GeneralizedPseudostandardPeriodicity.gap_bound
Declaration: closure_suffix_bound; proof_shape: bind-only; escape_witness: none
  consumer: closure_bounds, GeneralizedPseudostandardPeriodicity.gap_bound
Declaration: pre_length; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.border_read
Declaration: pre_get; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.pre_pal_read
Declaration: Generates.step; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.next_letter
Declaration: Generates.strict_growth; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.next_letter
Declaration: Generates.length_ge; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.border_periodic
Declaration: Generates.nested; proof_shape: bind-only; escape_witness: none
  consumer: Generates.nested_le
Declaration: Generates.nested_le; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.border_periodic
Declaration: Generates.pal; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.border_periodic
Declaration: Generates.read; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.next_letter
Declaration: IsNormalized; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.normalized_next_le
Declaration: InvAntimorphism.map_suffix_prefix; proof_shape: bind-only; escape_witness: none
  consumer: InvAntimorphism.extension_tail, InvAntimorphism.pal_suffix_prefix, closure_prefix
Declaration: InvAntimorphism.pal_suffix_prefix; proof_shape: bind-only; escape_witness: none
  consumer: closure_prefix
Declaration: finite_border_period; proof_shape: bind-only; escape_witness: none
  conclusion: the offset equality at each valid index; consumers: closure_prefix, GeneralizedPseudostandardPeriodicity.border_read
Declaration: twisted_border; proof_shape: bind-only; escape_witness: none
  consumer: closure_prefix
Declaration: period_extend_left; proof_shape: content; escape_witness: period_extend_left
  consumer: closure_prefix
Declaration: closure_prefix; proof_shape: content; escape_witness: period_extend_left
  consumer: earliest_insertion
Declaration: closure_insert_right; proof_shape: bind-only; escape_witness: none
  consumer: Generates.adjacent_prefix_closure
Declaration: EarliestPseudoPrefixAfter; proof_shape: bind-only; escape_witness: none
  consumer: earliest_insertion
Declaration: earliest_insertion; proof_shape: content; escape_witness: period_extend_left
  conclusion: IsClosure ψ (P ++ [a]) V; consumer: Generates.adjacent_prefix_closure
Declaration: pre_prefix; proof_shape: bind-only; escape_witness: none
  conclusion: the shorter finite prefix is a prefix of the longer one; consumer: Generates.adjacent_prefix_closure and GeneralizedPseudostandardPeriodicity.border_read
Declaration: pre_succ; proof_shape: bind-only; escape_witness: none
  consumer: Generates.adjacent_prefix_closure
Declaration: PseudoLength; proof_shape: bind-only; escape_witness: none
  consumer: Generates.adjacent_prefix_closure
Declaration: Generates.lengths_strictMono; proof_shape: bind-only; escape_witness: none
  consumer: GeneralizedPseudostandardPeriodicity.Generates.normalized_next_le
Declaration: Generates.pseudo_length; proof_shape: bind-only; escape_witness: none
  consumer: Generates.adjacent_prefix_closure
Declaration: Generates.pseudo_infinite; proof_shape: bind-only; escape_witness: none
  consumer: Generates.normalization_exists
Declaration: Generates.adjacent_prefix_closure; proof_shape: content; escape_witness:
  period_extend_left
  consumer: Generates.normalization_exists
Declaration: Generates.normalization_exists; proof_shape: content; escape_witness:
  period_extend_left
  consumer: GeneralizedPseudostandardPeriodicity.result
-/

import Mathlib.Algebra.Group.End
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Fin.Tuple.Take

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization

structure InvAntimorphism (α : Type*) where
  toFun : List α → List α
  map_append : ∀ v w, toFun (v ++ w) = toFun w ++ toFun v
  involutive : ∀ w, toFun (toFun w) = w

end D5.S1.Words.Palindromes.PseudopalindromicNormalization

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization
namespace InvAntimorphism
variable {α : Type*} (θ : InvAntimorphism α)

@[simp] private theorem map_nil : θ.toFun [] = [] := by
  have h := congrArg List.length (θ.map_append [] [])
  simp only [List.nil_append, List.length_append] at h
  exact List.length_eq_zero_iff.mp (by omega)

@[simp] private theorem map_eq_nil_iff (w : List α) : θ.toFun w = [] ↔ w = [] := by
  simpa only [InvAntimorphism.map_nil] using
    (show Function.Involutive θ.toFun from θ.involutive).eq_iff (x := w) (y := [])

private theorem length_lower (w : List α) : w.length ≤ (θ.toFun w).length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have hp : 0 < (θ.toFun [a]).length := List.length_pos_iff.mpr (by simp)
    have he := θ.map_append [a] w
    have hl := congrArg List.length he
    simp only [List.singleton_append, List.length_cons, List.length_append] at hl ⊢
    omega

@[simp] private theorem length_map (w : List α) : (θ.toFun w).length = w.length := by
  have h := (InvAntimorphism.length_lower θ) (θ.toFun w)
  rw [θ.involutive] at h
  exact Nat.le_antisymm h ((InvAntimorphism.length_lower θ) w)

theorem singletonExists (a : α) : ∃ b, θ.toFun [a] = [b] := by
  apply List.length_eq_one_iff.mp
  simp

noncomputable def letter (a : α) : α := Classical.choose ((InvAntimorphism.singletonExists θ) a)

@[simp] theorem map_singleton (a : α) : θ.toFun [a] = [(InvAntimorphism.letter θ) a] :=
  Classical.choose_spec ((InvAntimorphism.singletonExists θ) a)

@[simp] theorem letterInvolutive (a : α) : (InvAntimorphism.letter θ) ((InvAntimorphism.letter θ) a) = a := by
  have h := θ.involutive [a]
  simpa only [(InvAntimorphism.map_singleton θ), List.singleton_inj] using h

noncomputable def perm : Equiv.Perm α :=
  Function.Involutive.toPerm (InvAntimorphism.letter θ) (InvAntimorphism.letterInvolutive θ)

@[simp] theorem perm_apply (a : α) : (InvAntimorphism.perm θ) a = (InvAntimorphism.letter θ) a :=
  congrFun (Function.Involutive.coe_toPerm (InvAntimorphism.letterInvolutive θ)) a

theorem perm_unique (π : Equiv.Perm α)
    (h : ∀ w, θ.toFun w = (w.map π).reverse) : π = (InvAntimorphism.perm θ) := by
  ext a
  simpa using (h [a]).symm

private theorem representation : ∃ π : Equiv.Perm α,
    ∀ w, θ.toFun w = (w.map π).reverse := by
  have hword (w : List α) : θ.toFun w = (w.map θ.perm).reverse := by
    induction w with
    | nil => simp
    | cons a w ih =>
      simpa only [List.singleton_append, List.map_cons, List.reverse_cons, perm_apply]
        using (θ.map_append [a] w).trans (by rw [ih, (InvAntimorphism.map_singleton θ)])
  exact ⟨θ.perm, hword⟩

@[simp] theorem map_word (w : List α) : θ.toFun w = (w.map (InvAntimorphism.perm θ)).reverse := by
  obtain ⟨π, hw⟩ := θ.representation
  have he := θ.perm_unique π hw
  simpa only [he] using hw w

end InvAntimorphism
end D5.S1.Words.Palindromes.PseudopalindromicNormalization

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization
variable {α : Type*}

theorem pal_wrap (θ : InvAntimorphism α) (p s : List α) (hs : Function.IsFixedPt θ.toFun s) :
    Function.IsFixedPt θ.toFun (p ++ s ++ θ.toFun p) := by
  unfold Function.IsFixedPt at *
  rw [θ.map_append, θ.map_append, θ.involutive, hs]
  simp only [List.append_assoc]

private theorem two_letter_pal (θ : InvAntimorphism α) (a : α) :
    Function.IsFixedPt θ.toFun [a, (InvAntimorphism.letter θ) a] := by
  simpa only [List.append_nil, InvAntimorphism.map_singleton, List.singleton_append] using
    pal_wrap θ [a] [] (InvAntimorphism.map_nil θ)

theorem palindrome_transport_iff (θ σ τ : InvAntimorphism α) :
    (∀ w, Function.IsFixedPt θ.toFun w → Function.IsFixedPt τ.toFun (σ.toFun w)) ↔
      (InvAntimorphism.perm τ) = (InvAntimorphism.perm σ) * (InvAntimorphism.perm θ) * (InvAntimorphism.perm σ) := by
  constructor
  · intro h
    ext a
    have ht := h [(InvAntimorphism.letter σ) a, (InvAntimorphism.letter θ) ((InvAntimorphism.letter σ) a)] (two_letter_pal θ _)
    simp only [Function.IsFixedPt, InvAntimorphism.map_word, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      InvAntimorphism.perm_apply, InvAntimorphism.letterInvolutive] at ht
    have hh := congrArg List.head? ht
    simpa using hh
  · intro h w hw
    have hc (a : α) : (InvAntimorphism.perm τ) ((InvAntimorphism.perm σ) a) = (InvAntimorphism.perm σ) ((InvAntimorphism.perm θ) a) := by
      rw [h]
      simp [Equiv.Perm.mul_apply, InvAntimorphism.perm_apply]
    have ht : τ.toFun (σ.toFun w) = σ.toFun (θ.toFun w) := by
      simp only [InvAntimorphism.map_word, List.map_reverse, List.reverse_reverse,
        List.map_map]
      congr 1
      funext a
      exact hc a
    exact ht.trans (congrArg σ.toFun hw)

end D5.S1.Words.Palindromes.PseudopalindromicNormalization

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization
variable {α : Type*}
namespace InvAntimorphism

theorem prefix_to_suffix (σ : InvAntimorphism α) (P Q : List α)
    (hp : P <+: Q) (hq : Function.IsFixedPt σ.toFun Q) : σ.toFun P <:+ Q := by
  obtain ⟨r, rfl⟩ := hp
  exact ⟨σ.toFun r, by simpa only [Function.IsFixedPt, σ.map_append] using hq⟩

end InvAntimorphism
end D5.S1.Words.Palindromes.PseudopalindromicNormalization

open D5.S1.Words.Palindromes

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization

def IsClosure (θ : InvAntimorphism α) (w z : List α) : Prop :=
  w <+: z ∧ θ.toFun z = z ∧
    ∀ z', w <+: z' → θ.toFun z' = z' → z.length ≤ z'.length

def Generates (δ : ℕ → α) (Θ : ℕ → InvAntimorphism α)
    (u : ℕ → α) (W : ℕ → List α) : Prop :=
  W 0 = [] ∧
    (∀ n, IsClosure (Θ (n + 1)) (W n ++ [δ (n + 1)]) (W (n + 1))) ∧
    ∀ n, W n = (List.ofFn (fun i : Fin (W n).length => u i))

end D5.S1.Words.Palindromes.PseudopalindromicNormalization

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization
variable {α : Type*}

namespace InvAntimorphism

private theorem map_suffix_prefix (θ : InvAntimorphism α) (P Q : List α)
    (hs : P <:+ Q) : θ.toFun P <+: θ.toFun Q := by
  obtain ⟨r, rfl⟩ := hs
  exact ⟨θ.toFun r, (θ.map_append r P).symm⟩

private theorem extension_tail (θ : InvAntimorphism α) (w r : List α)
    (h : Function.IsFixedPt θ.toFun (w ++ r)) (hr : r.length ≤ w.length) :
    θ.toFun r = w.take r.length := by
  have hp : θ.toFun r <+: w ++ r := by
    simpa only [show θ.toFun (w ++ r) = w ++ r from h] using
      InvAntimorphism.map_suffix_prefix θ r (w ++ r) (List.suffix_append w r)
  have hpw : θ.toFun r <+: w :=
    List.prefix_of_prefix_length_le hp (List.prefix_append w r) (by simpa)
  simpa using List.prefix_iff_eq_take.mp hpw

private theorem extension_overlap (θ : InvAntimorphism α) (w r : List α)
    (h : Function.IsFixedPt θ.toFun (w ++ r)) (hr : r.length ≤ w.length) :
    Function.IsFixedPt θ.toFun (w.drop r.length) := by
  have ht := (InvAntimorphism.extension_tail θ) w r h hr
  have htr : θ.toFun (w.take r.length) = r := by
    rw [← ht, θ.involutive]
  have he : (w.take r.length ++ w.drop r.length) ++ r =
      w.take r.length ++ θ.toFun (w.drop r.length) ++ r := by
    calc
      (w.take r.length ++ w.drop r.length) ++ r = w ++ r := by
        rw [List.take_append_drop]
      _ = θ.toFun r ++ θ.toFun w := by
        simpa only [Function.IsFixedPt, θ.map_append] using h.symm
      _ = w.take r.length ++ θ.toFun (w.drop r.length) ++ r := by
        have hd : θ.toFun w = θ.toFun (w.drop r.length) ++ θ.toFun (w.take r.length) := by
          rw [← θ.map_append, List.take_append_drop]
        rw [ht, hd, htr]
        simp only [List.append_assoc]
  exact (List.append_cancel_left (List.append_cancel_right he)).symm

end InvAntimorphism

private noncomputable def cut (θ : InvAntimorphism α) (w : List α) : ℕ := by
  classical
  exact Nat.find (show ∃ n, Function.IsFixedPt θ.toFun (w.drop n) from
    ⟨w.length, by simp [Function.IsFixedPt]⟩)

private theorem cut_spec (θ : InvAntimorphism α) (w : List α) :
    Function.IsFixedPt θ.toFun (w.drop (cut θ w)) := by
  classical
  exact Nat.find_spec (p := fun n => Function.IsFixedPt θ.toFun (w.drop n)) _

private theorem cut_min (θ : InvAntimorphism α) (w : List α) (n : ℕ)
    (h : Function.IsFixedPt θ.toFun (w.drop n)) : cut θ w ≤ n := by
  classical
  exact Nat.find_min' (p := fun n => Function.IsFixedPt θ.toFun (w.drop n)) _ h

private theorem cut_le_length (θ : InvAntimorphism α) (w : List α) : cut θ w ≤ w.length :=
  cut_min θ w w.length (by simp [Function.IsFixedPt])

private noncomputable def closure (θ : InvAntimorphism α) (w : List α) : List α :=
  w ++ θ.toFun (w.take (cut θ w))

private theorem closure_pal (θ : InvAntimorphism α) (w : List α) : Function.IsFixedPt θ.toFun (closure θ w) := by
  simpa only [closure, List.append_assoc, List.take_append_drop] using
    pal_wrap θ (w.take (cut θ w)) (w.drop (cut θ w)) (cut_spec θ w)

private theorem closure_length (θ : InvAntimorphism α) (w : List α) :
    (closure θ w).length = w.length + cut θ w := by
  simp [closure, List.length_take, Nat.min_eq_left (cut_le_length θ w)]

private theorem closure_spec (θ : InvAntimorphism α) (w : List α) :
    IsClosure θ w (closure θ w) := by
  refine ⟨List.prefix_append _ _, closure_pal θ w, ?_⟩
  intro z hz hp
  obtain ⟨r, rfl⟩ := hz
  by_cases hr : r.length ≤ w.length
  · have hc := cut_min θ w r.length ((InvAntimorphism.extension_overlap θ) w r hp hr)
    rw [closure_length, List.length_append]
    omega
  · have hc := cut_le_length θ w
    rw [closure_length, List.length_append]
    omega

end D5.S1.Words.Palindromes.PseudopalindromicNormalization

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization
variable {α : Type*}

theorem closure_suffix_bound (θ : InvAntimorphism α) (w z s : List α)
    (hz : IsClosure θ w z) (hs : s <:+ w) (hp : Function.IsFixedPt θ.toFun s) :
    z.length + s.length ≤ 2 * w.length := by
  obtain ⟨p, rfl⟩ := hs
  have hm := hz.2.2 (p ++ s ++ θ.toFun p) (List.prefix_append _ _) (pal_wrap θ p s hp)
  simp only [List.length_append, InvAntimorphism.length_map] at hm ⊢
  omega

private theorem closure_bounds (θ : InvAntimorphism α) (w z : List α)
    (h : IsClosure θ w z) : z.length ≤ 2 * w.length := by
  simpa only [List.length_nil, Nat.add_zero] using
    closure_suffix_bound θ w z [] h List.nil_suffix (InvAntimorphism.map_nil θ)

end D5.S1.Words.Palindromes.PseudopalindromicNormalization

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization
variable {α : Type*}

@[simp] theorem pre_length (u : ℕ → α) (m : ℕ) : ((List.ofFn (fun i : Fin m => u i))).length = m := by
  exact List.length_ofFn

@[simp] theorem pre_get (u : ℕ → α) (m j : ℕ) (h : j < ((List.ofFn (fun i : Fin m => u i))).length) :
    ((List.ofFn (fun i : Fin m => u i)))[j] = u j := by
  exact List.getElem_ofFn h

namespace Generates
variable {δ : ℕ → α} {Θ : ℕ → InvAntimorphism α}
    {u : ℕ → α} {W : ℕ → List α} (h : Generates δ Θ u W)
include h

theorem step (n : ℕ) :
    IsClosure (Θ (n + 1)) (W n ++ [δ (n + 1)]) (W (n + 1)) := h.2.1 n

theorem strict_growth (n : ℕ) : (W n).length < (W (n + 1)).length := by
  have hp := (h.step n).1.length_le
  simp only [List.length_append, List.length_singleton] at hp
  omega

theorem length_ge (n : ℕ) : n ≤ (W n).length := by
  exact StrictMono.id_le (strictMono_nat_of_lt_succ (Generates.strict_growth h)) n

private theorem nested (n : ℕ) : W n <+: W (n + 1) :=
  (List.prefix_append _ _).trans (h.step n).1

theorem nested_le {m n : ℕ} (hmn : m ≤ n) : W m <+: W n := by
  induction n, hmn using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n hn ih => exact ih.trans (h.nested n)

theorem pal (n : ℕ) (hn : 1 ≤ n) : Function.IsFixedPt (Θ n).toFun (W n) := by
  have hp := (h.step (n - 1)).2.1
  simpa only [Function.IsFixedPt, Nat.sub_add_cancel hn] using hp

theorem read (n j : ℕ) (hj : j < (W n).length) : (W n)[j] = u j := by
  rw [List.getElem_of_eq (h.2.2 n) hj]
  exact pre_get _ _ _ _

end Generates
end D5.S1.Words.Palindromes.PseudopalindromicNormalization

open D5.S1.Words.Palindromes

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization

def IsNormalized (u : ℕ → α) (W : ℕ → List α) : Prop :=
  ∀ m, (∃ θ : InvAntimorphism α,
    θ.toFun (List.ofFn (fun i : Fin m => u i)) = List.ofFn (fun i : Fin m => u i)) →
      ∃ n, W n = List.ofFn (fun i : Fin m => u i)

end D5.S1.Words.Palindromes.PseudopalindromicNormalization

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization
variable {α : Type*}

namespace InvAntimorphism

private theorem pal_suffix_prefix (θ : InvAntimorphism α) (P Q : List α)
    (hs : P <:+ Q) (hp : Function.IsFixedPt θ.toFun P) (hq : Function.IsFixedPt θ.toFun Q) : P <+: Q := by
  have ht := (InvAntimorphism.map_suffix_prefix θ) P Q hs
  unfold Function.IsFixedPt at hp hq
  simpa only [hp, hq] using ht

end InvAntimorphism

theorem finite_border_period (P Q : List α) (hp : P <+: Q) (hs : P <:+ Q)
    (d : ℕ) (hd : P.length + d = Q.length) (j : ℕ) (hj : j + d < Q.length) :
    Q[j + d] = Q[j]'(by omega) := by
  have hjp : j < P.length := by omega
  have he := List.suffix_iff_eq_drop.mp hs
  have heq : Q.length - P.length = d := by omega
  rw [heq] at he
  have hh := List.getElem_of_eq he hjp
  simp only [List.getElem_drop] at hh
  have hi : d + j = j + d := by omega
  simpa only [hi] using hh.symm.trans (hp.getElem hjp)

private theorem twisted_border (θ ψ : InvAntimorphism α) (V W : List α)
    (hv : Function.IsFixedPt ψ.toFun V) (hw : Function.IsFixedPt θ.toFun W) (hp : V <+: W)
    (q : ℕ) (hq : V.length + q = W.length)
    (j : ℕ) (hj : j + q < W.length) :
    W[j + q] = (PseudopalindromicNormalization.InvAntimorphism.perm θ) ((PseudopalindromicNormalization.InvAntimorphism.perm ψ) (W[j]'(by omega))) := by
  have hs := (PseudopalindromicNormalization.InvAntimorphism.prefix_to_suffix θ) V W hp hw
  have he := List.suffix_iff_eq_drop.mp hs
  have hi : W.length - (θ.toFun V).length = q := by
    rw [(PseudopalindromicNormalization.InvAntimorphism.length_map θ)]; omega
  rw [hi] at he
  have hl : j < V.length := by omega
  have htt : θ.toFun V = V.map ((PseudopalindromicNormalization.InvAntimorphism.perm θ) * (PseudopalindromicNormalization.InvAntimorphism.perm ψ)) := by
    calc
      θ.toFun V = θ.toFun (ψ.toFun V) := congrArg θ.toFun hv.symm
      _ = V.map ((PseudopalindromicNormalization.InvAntimorphism.perm θ) * (PseudopalindromicNormalization.InvAntimorphism.perm ψ)) := by
        simp only [(PseudopalindromicNormalization.InvAntimorphism.map_word ψ), (PseudopalindromicNormalization.InvAntimorphism.map_word θ), List.map_reverse,
          List.reverse_reverse, List.map_map]
        rfl
  have hh := congrArg (fun w : List α => w[j]?) he
  rw [htt] at hh
  have hh' : (PseudopalindromicNormalization.InvAntimorphism.perm θ) ((PseudopalindromicNormalization.InvAntimorphism.perm ψ) (V[j]'hl)) = W[j + q] := by
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some,
      Equiv.Perm.mul_apply, List.getElem?_drop, List.getElem?_eq_getElem hj,
      show q + j = j + q by omega, Option.some.injEq] using hh
  rw [← hh', hp.getElem hl]

private theorem period_extend_left (A : List α) (k d q : ℕ) (f : α → α)
    (hf : Function.Injective f) (hq : 0 < q) (hb : k + q + d ≤ A.length)
    (ht : ∀ j (hj : j + q < A.length),
      A[j + q] = f (A[j]'(by omega)))
    (hp : ∀ j, k ≤ j → ∀ (hj : j + d < A.length), A[j + d] = A[j]'(by omega)) :
    ∀ j (hj : j + d < A.length), A[j + d] = A[j]'(by omega) := by
  intro j hj
  induction e : k - j using Nat.strong_induction_on generalizing j with
  | h n ih =>
    by_cases hk : k ≤ j
    · exact hp j hk hj
    · have hs : k - (j + q) < n := by omega
      have hb' : j + q + d < A.length := by omega
      have hnext := ih (k - (j + q)) hs (j + q) hb' rfl
      apply hf
      have h1 := ht (j + d) (by omega)
      have h2 := ht j (by omega)
      have he : j + q + d = j + d + q := by omega
      have hnext' : A[j + d + q]'(by omega) = A[j + q]'(by omega) := by
        simpa only [he] using hnext
      exact h1.symm.trans (hnext'.trans h2)

end D5.S1.Words.Palindromes.PseudopalindromicNormalization

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization
variable {α : Type*}

private theorem closure_prefix (θ ψ : InvAntimorphism α) (A V W : List α)
    (hc : IsClosure θ A W) (hav : A <+: V) (hvw : V <+: W)
    (hv : Function.IsFixedPt ψ.toFun V) (hm : V.length < W.length) :
    closure ψ A <+: V := by
  obtain ⟨r, rfl⟩ := hav
  let k := cut ψ A
  let d := r.length - k
  let q := W.length - (A ++ r).length
  have hbound := closure_bounds θ A W hc
  have hpre := hvw.length_le
  simp only [List.length_append] at hpre hm
  have hr : r.length ≤ A.length := by omega
  have hk0 : k ≤ A.length := cut_le_length ψ A
  have htpal := (PseudopalindromicNormalization.InvAntimorphism.extension_overlap ψ) A r hv hr
  have hk : k ≤ r.length := cut_min ψ A _ htpal
  have hd : k + d = r.length := by dsimp [d]; omega
  have hq : 0 < q := by dsimp [q]; simp only [List.length_append]; omega
  have hqeq : (A ++ r).length + q = W.length := by dsimp [q]; omega
  have hb : k + q + d ≤ A.length := by
    dsimp [q]
    simp only [List.length_append]
    omega
  have hts : A.drop r.length <:+ A.drop k := by
    have he : r.length = k + (r.length - k) := by omega
    rw [he, ← List.drop_drop]
    exact List.drop_suffix _ _
  have htpre : A.drop r.length <+: A.drop k :=
    (InvAntimorphism.pal_suffix_prefix ψ) _ _ hts htpal (cut_spec ψ A)
  have htl : (A.drop r.length).length + d = (A.drop k).length := by
    simp only [List.length_drop]
    omega
  have hp : ∀ j, k ≤ j → ∀ (hj : j + d < A.length),
      A[j + d] = A[j]'(by omega) := by
    intro j hjk hj
    have hjS : j - k + d < (A.drop k).length := by
      simp only [List.length_drop]; omega
    have hh := finite_border_period _ _ htpre hts d htl (j - k) hjS
    have he1 : k + (j - k + d) = j + d := by omega
    have he2 : k + (j - k) = j := by omega
    simpa only [List.getElem_drop, he1, he2] using hh
  have htw : ∀ j (hj : j + q < A.length),
      A[j + q] = (PseudopalindromicNormalization.InvAntimorphism.perm θ) ((PseudopalindromicNormalization.InvAntimorphism.perm ψ) (A[j]'(by omega))) := by
    intro j hj
    have hjW : j + q < W.length := by have := hc.1.length_le; omega
    have hh := twisted_border θ ψ (A ++ r) W hv hc.2.1 hvw q hqeq j hjW
    calc
      A[j + q] = W[j + q] := hc.1.getElem hj
      _ = (PseudopalindromicNormalization.InvAntimorphism.perm θ) ((PseudopalindromicNormalization.InvAntimorphism.perm ψ) (W[j]'(by omega))) := hh
      _ = (PseudopalindromicNormalization.InvAntimorphism.perm θ) ((PseudopalindromicNormalization.InvAntimorphism.perm ψ) (A[j]'(by omega))) :=
        congrArg (fun a => (PseudopalindromicNormalization.InvAntimorphism.perm θ) ((PseudopalindromicNormalization.InvAntimorphism.perm ψ) a)) (hc.1.getElem (by omega)).symm
  have hall := period_extend_left A k d q (fun a => (PseudopalindromicNormalization.InvAntimorphism.perm θ) ((PseudopalindromicNormalization.InvAntimorphism.perm ψ) a))
    ((PseudopalindromicNormalization.InvAntimorphism.perm θ).injective.comp (PseudopalindromicNormalization.InvAntimorphism.perm ψ).injective) hq hb htw hp
  have htt : A.take k <:+ A.take r.length := by
    apply List.suffix_iff_eq_drop.mpr
    simp only [List.length_take, Nat.min_eq_left hr, Nat.min_eq_left hk0]
    change A.take k = (A.take r.length).drop d
    apply List.ext_getElem
    · simp only [List.length_take, Nat.min_eq_left hr, Nat.min_eq_left hk0,
        List.length_drop]
      omega
    · intro j hj hj'
      have hjk : j < k := by simpa only [List.length_take, Nat.min_eq_left hk0] using hj
      have hjd : j + d < A.length := by omega
      have he := hall j hjd
      simpa only [List.getElem_drop, List.getElem_take,
        show d + j = j + d by omega] using he.symm
  have htmap := (InvAntimorphism.map_suffix_prefix ψ) (A.take k) (A.take r.length) htt
  have hrt : r = ψ.toFun (A.take r.length) := by
    have he := (PseudopalindromicNormalization.InvAntimorphism.extension_tail ψ) A r hv hr
    rw [← he, ψ.involutive]
  obtain ⟨s, hs⟩ := htmap
  refine ⟨s, ?_⟩
  change (A ++ ψ.toFun (A.take k)) ++ s = A ++ r
  rw [List.append_assoc, hs, ← hrt]

end D5.S1.Words.Palindromes.PseudopalindromicNormalization

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization
variable {α : Type*}

private theorem closure_insert_right (θ : InvAntimorphism α) (A B W : List α)
    (h : IsClosure θ A W) (hab : A <+: B) (hbw : B <+: W) :
    IsClosure θ B W := by
  refine ⟨hbw, h.2.1, ?_⟩
  intro z hz hp
  exact h.2.2 z (hab.trans hz) hp

private def EarliestPseudoPrefixAfter (P V : List α) : Prop :=
  P.length < V.length ∧
    ∀ z, z <+: V → P.length < z.length → z.length < V.length →
      ∀ ψ : InvAntimorphism α, ¬ Function.IsFixedPt ψ.toFun z

private theorem earliest_insertion (θ ψ : InvAntimorphism α) (P V W : List α) (a : α)
    (hW : IsClosure θ (P ++ [a]) W) (hVW : V <+: W) (hV : Function.IsFixedPt ψ.toFun V)
    (hE : EarliestPseudoPrefixAfter P V) (hU : V.length < W.length) :
    IsClosure ψ (P ++ [a]) V := by
  have hAV : P ++ [a] <+: V :=
    List.prefix_of_prefix_length_le hW.1 hVW (by
      have hL := hE.1
      simp only [List.length_append, List.length_singleton]
      omega)
  have hCV := closure_prefix θ ψ (P ++ [a]) V W hW hAV hVW hV hU
  have hC := closure_spec ψ (P ++ [a])
  have hmin : V.length ≤ (closure ψ (P ++ [a])).length := by
    by_contra hn
    have hlen := hC.1.length_le
    simp only [List.length_append, List.length_singleton] at hlen
    exact hE.2 _ hCV (by omega) (by omega) ψ hC.2.1
  have he := hCV.eq_of_length (Nat.le_antisymm hCV.length_le hmin)
  rw [← he]
  exact hC

end D5.S1.Words.Palindromes.PseudopalindromicNormalization

namespace D5.S1.Words.Palindromes.PseudopalindromicNormalization
variable {α : Type*}

theorem pre_prefix (u : ℕ → α) {m n : ℕ} (h : m ≤ n) : (List.ofFn (fun i : Fin m => u i)) <+: (List.ofFn (fun i : Fin n => u i)) := by
  apply List.prefix_iff_eq_take.mpr
  have ht := Fin.ofFn_take_eq_take_ofFn h (fun i : Fin n => u i)
  convert ht using 1
  · rfl
  · simp

private theorem pre_succ (u : ℕ → α) (m : ℕ) : (List.ofFn (fun i : Fin (m + 1) => u i)) = (List.ofFn (fun i : Fin m => u i)) ++ [u m] := List.ofFn_succ_last

private def PseudoLength (u : ℕ → α) (m : ℕ) : Prop :=
  ∃ θ : InvAntimorphism α, Function.IsFixedPt θ.toFun ((List.ofFn (fun i : Fin m => u i)))

namespace Generates
variable {δ : ℕ → α} {Θ : ℕ → InvAntimorphism α}
    {u : ℕ → α} {W : ℕ → List α} (hg : Generates δ Θ u W)
include hg

theorem lengths_strictMono : StrictMono (fun n => (W n).length) :=
  strictMono_nat_of_lt_succ (PseudopalindromicNormalization.Generates.strict_growth hg)

private theorem pseudo_length (n : ℕ) : PseudoLength u (W n).length := by
  cases n with
  | zero => refine ⟨Θ 0, ?_⟩; simp [hg.1, Function.IsFixedPt]
  | succ n => exact ⟨Θ (n + 1), by rw [← hg.2.2]; exact (PseudopalindromicNormalization.Generates.pal hg) _ (by omega)⟩

private theorem pseudo_infinite : (Set.ofPred (PseudoLength u)).Infinite := by
  apply Set.infinite_of_injective_forall_mem (Generates.lengths_strictMono hg).injective
  exact (Generates.pseudo_length hg)

private theorem adjacent_prefix_closure (m n : ℕ) (hmn : m < n)
    (hn : PseudoLength u n)
    (he : ∀ z, m < z → z < n → ¬ PseudoLength u z) :
    ∃ ψ : InvAntimorphism α, IsClosure ψ ((List.ofFn (fun i : Fin m => u i)) ++ [u m]) ((List.ofFn (fun i : Fin n => u i))) := by
  classical
  have hex : ∃ j, m < (W (j + 1)).length :=
    ⟨m, lt_of_lt_of_le (by omega) ((PseudopalindromicNormalization.Generates.length_ge hg) (m + 1))⟩
  let j := Nat.find hex
  have hj : m < (W (j + 1)).length := Nat.find_spec hex
  have hj0 : (W j).length ≤ m := by
    cases h : j with
    | zero => simp [hg.1]
    | succ k =>
      have hh := Nat.find_min hex (show k < Nat.find hex by omega)
      simp only [not_lt] at hh
      simpa only [h] using hh
  have hnW : n ≤ (W (j + 1)).length := by
    by_contra hh
    exact he _ hj (by omega) ((Generates.pseudo_length hg) _)
  have hp : (List.ofFn (fun i : Fin (m + 1) => u i)) <+: W (j + 1) := by
    rw [hg.2.2]; exact pre_prefix u (by omega)
  have ha : W j ++ [δ (j + 1)] <+: (List.ofFn (fun i : Fin (m + 1) => u i)) :=
    List.prefix_of_prefix_length_le ((PseudopalindromicNormalization.Generates.step hg) j).1 hp (by simp; omega)
  have hc : IsClosure (Θ (j + 1)) ((List.ofFn (fun i : Fin m => u i)) ++ [u m]) (W (j + 1)) := by
    rw [← pre_succ]
    exact closure_insert_right _ _ _ _ ((PseudopalindromicNormalization.Generates.step hg) j) ha hp
  by_cases hnEq : n = (W (j + 1)).length
  · refine ⟨Θ (j + 1), ?_⟩
    rw [hnEq, ← hg.2.2 (j + 1)]
    exact hc
  · obtain ⟨ψ, hψ⟩ := hn
    refine ⟨ψ, earliest_insertion (Θ (j + 1)) ψ ((List.ofFn (fun i : Fin m => u i))) ((List.ofFn (fun i : Fin n => u i)))
      (W (j + 1)) (u m) hc ?_ hψ ?_ (by simpa using lt_of_le_of_ne hnW hnEq)⟩
    · rw [hg.2.2]; exact pre_prefix u hnW
    · refine ⟨by simpa using hmn, ?_⟩
      intro z hz hmz hzn σ hσ
      have hzEq : z = (List.ofFn (fun i : Fin z.length => u i)) := by
        apply List.ext_getElem
        · simp
        · intro i hi hi'
          rw [pre_get]
          exact (hz.getElem hi).trans (pre_get _ _ _ _)
      exact he z.length (by simpa using hmz) (by simpa using hzn)
        ⟨σ, by rwa [← hzEq]⟩

theorem normalization_exists :
    ∃ δ' Θ' W', Generates δ' Θ' u W' ∧ IsNormalized u W' := by
  classical
  let L := Nat.nth (PseudoLength u)
  have hInf := (Generates.pseudo_infinite hg)
  have hMono : StrictMono L := Nat.nth_strictMono hInf
  have hMem : ∀ n, PseudoLength u (L n) := Nat.nth_mem_of_infinite hInf
  have hAdj (n : ℕ) : ∃ ψ : InvAntimorphism α,
      IsClosure ψ ((List.ofFn (fun i : Fin (L n) => u i)) ++ [u (L n)]) ((List.ofFn (fun i : Fin (L (n + 1)) => u i))) := by
    apply (Generates.adjacent_prefix_closure hg) _ _ (hMono (by omega)) (hMem _)
    intro z hm hz hp
    exact (not_lt_of_ge (Nat.le_nth_of_lt_nth_succ hz hp)) hm
  let Ψ (n : ℕ) := Classical.choose (hAdj n)
  let δ' (n : ℕ) := u (L (n - 1))
  let Θ' (n : ℕ) := Ψ (n - 1)
  let W' (n : ℕ) := (List.ofFn (fun i : Fin (L n) => u i))
  refine ⟨δ', Θ', W', ⟨?_, ?_, ?_⟩, ?_⟩
  · have h0 : PseudoLength u 0 := ⟨Θ 0, by simp [Function.IsFixedPt]⟩
    simp [W', L, Nat.nth_zero_of_zero h0]
  · intro n
    simpa only [W', δ', Θ', Nat.add_sub_cancel_right] using Classical.choose_spec (hAdj n)
  · intro n; simp [W']
  · intro m hm
    have hr : m ∈ Set.range L := by
      rw [Nat.range_nth_of_infinite hInf]; exact hm
    obtain ⟨n, hn⟩ := hr
    exact ⟨n, by subst m; rfl⟩

end Generates
end D5.S1.Words.Palindromes.PseudopalindromicNormalization
