/- GID: D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiFixedPoints
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiFixedPoints
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: Pseudo-Frobenius row deletion fixes exactly the symmetric numerical semigroups, which are almost symmetric. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#457)
escape_witness: pf_above (every gap lies below a pseudo-Frobenius number at a semigroup
  distance), symmetric_type_one and type_one_symmetric (symmetry is equivalent to
  PF(S) = {F(S)}, the forward direction for every numerical set) and symmetric_genus (the
  reflection a -> F - a gives 2g = F + 1); result combines them with the cardinality of the
  row deletion.
proof_shape:
  frob_mem, le_frob, zero_mem, frob_pf: bind-only helpers; consumers: pf_above,
    symmetric_type_one, type_one_symmetric, symmetric_genus, result.
  pf_above: content; consumer: type_one_symmetric.
  symmetric_type_one, type_one_symmetric: content; consumer: result.
  phi_of_type_one: bind-only (no retained row is deleted); consumer: result.
  symmetric_genus: content; consumer: result.
  result: content.
Direct frozen dependencies: D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation
  (NumericalSet, members, frobenius, Semigroup, PseudoFrobenius, AlmostSymmetric, Symmetric,
  retainedRows, deleteRows, phi).
Search record (§3.1): the frozen module proves phi_omits_one and non-surjectivity only; no D5
  module or pinned Mathlib declaration characterizes symmetric numerical semigroups by their
  pseudo-Frobenius set or the fixed points of the row deletion.
-/

import D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation
import Mathlib.Tactic

/-! # Fixed points of pseudo-Frobenius row deletion

Every symmetric numerical set is fixed by the row deletion `Φ`, has its Frobenius number `F` as
its only pseudo-Frobenius number and has genus `(F + 1) / 2`. For a proper numerical semigroup
`S`, conversely, `Φ(S) = S` exactly when `S` is symmetric, exactly when `F` is its only
pseudo-Frobenius number, and a symmetric `S` is almost symmetric.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints

open D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiRefutation

variable (U : NumericalSet)

private lemma frob_mem : frobenius U ∈ U.gaps := Finset.max'_mem _ _

private lemma le_frob {g : ℕ} (hg : g ∈ U.gaps) : g ≤ frobenius U := Finset.le_max' _ _ hg

private lemma zero_mem : 0 ∈ members U := U.zero_not_gap

/-- Every gap `a` lies below a pseudo-Frobenius number `f` with `f - a` in the semigroup. -/
private lemma pf_above (hS : Semigroup U) {a : ℕ} (ha : a ∈ U.gaps) :
    ∃ f, PseudoFrobenius U f ∧ a ≤ f ∧ f - a ∈ members U := by
  classical
  let G := U.gaps.filter (fun g => a ≤ g ∧ g - a ∈ members U)
  have haG : a ∈ G := Finset.mem_filter.mpr ⟨ha, le_rfl, by simpa using zero_mem U⟩
  have hG : G.Nonempty := ⟨a, haG⟩
  obtain ⟨hfg, haf, hfa⟩ := Finset.mem_filter.mp (Finset.max'_mem G hG)
  refine ⟨G.max' hG, ⟨hfg, fun s hs hsm => ?_⟩, haf, hfa⟩
  by_contra hn
  have hmem : G.max' hG + s ∈ G := by
    refine Finset.mem_filter.mpr ⟨by simpa [members] using hn, by omega, ?_⟩
    have := hS _ _ hfa hsm
    rwa [show G.max' hG + s - a = G.max' hG - a + s by omega]
  have := Finset.le_max' G _ hmem
  omega

/-- The Frobenius number is pseudo-Frobenius. -/
private lemma frob_pf : PseudoFrobenius U (frobenius U) := by
  refine ⟨frob_mem U, fun s hs _ => ?_⟩
  intro hg
  have := le_frob U hg
  omega

/-- In a symmetric numerical set the Frobenius number is the only pseudo-Frobenius number. -/
private lemma symmetric_type_one (hsym : Symmetric U) :
    ∀ f, PseudoFrobenius U f → f = frobenius U := by
  intro f hf
  by_contra hne
  have hfF : f < frobenius U := lt_of_le_of_ne (le_frob U hf.1) hne
  have hc : frobenius U - f ∈ members U := by
    by_contra h
    exact (hsym f hfF.le).mpr h hf.1
  have := hf.2 (frobenius U - f) (by omega) hc
  rw [show f + (frobenius U - f) = frobenius U by omega] at this
  exact this (frob_mem U)

/-- A semigroup whose only pseudo-Frobenius number is its Frobenius number is symmetric. -/
private lemma type_one_symmetric (hS : Semigroup U)
    (hone : ∀ f, PseudoFrobenius U f → f = frobenius U) : Symmetric U := by
  intro a ha
  constructor
  · intro ham hm
    have := hS _ _ ham hm
    rw [show a + (frobenius U - a) = frobenius U by omega] at this
    exact this (frob_mem U)
  · intro hn
    have hg : frobenius U - a ∈ U.gaps := by simpa [members] using hn
    obtain ⟨f, hf, -, hfm⟩ := pf_above U hS hg
    rw [hone f hf, show frobenius U - (frobenius U - a) = a by omega] at hfm
    exact hfm

/-- Without deleted rows, `Φ` returns the numerical set itself. -/
private lemma phi_of_type_one (hone : ∀ f, PseudoFrobenius U f → f = frobenius U) :
    phi U = members U := by
  classical
  have hR : retainedRows U = U.gaps := by
    unfold retainedRows
    apply Finset.filter_true_of_mem
    intro r _
    by_cases hp : PseudoFrobenius U r
    · exact Or.inl (hone r hp)
    · exact Or.inr hp
  unfold phi
  rw [hR]
  ext n
  simp only [deleteRows, Finset.sdiff_self, Finset.filter_empty, Finset.card_empty,
    Nat.sub_zero, Finset.image_id', Set.mem_ofPred_eq, members]

/-- A symmetric numerical set has `2g = F + 1`. -/
private lemma symmetric_genus (hsym : Symmetric U) : 2 * U.gaps.card = frobenius U + 1 := by
  classical
  set F := frobenius U
  let A := Finset.range (F + 1)
  have hgA : U.gaps = A.filter (fun a => a ∉ members U) := by
    ext a
    simp only [A, Finset.mem_filter, Finset.mem_range, members, Set.mem_ofPred_eq, not_not]
    exact ⟨fun h => ⟨Nat.lt_succ_of_le (le_frob U h), h⟩, fun h => h.2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun a => a ∈ members U)
  rw [Finset.card_range] at hsplit
  have hbij : (A.filter (fun a => a ∈ members U)).card =
      (A.filter (fun a => a ∉ members U)).card := by
    apply Finset.card_nbij' (fun a => F - a) (fun a => F - a)
    · intro a ha
      simp only [A, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha ⊢
      exact ⟨by omega, (hsym a (by omega)).mp ha.2⟩
    · intro a ha
      simp only [A, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha ⊢
      refine ⟨by omega, ?_⟩
      exact (hsym (F - a) (by omega)).mpr (by rw [show F - (F - a) = a by omega]; exact ha.2)
    · intro a ha
      simp only [A, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha
      dsimp only
      omega
    · intro a ha
      simp only [A, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ha
      dsimp only
      omega
  rw [hgA]
  omega

/-- Every symmetric numerical set is fixed by `Φ`, has `F` as its only pseudo-Frobenius
number and has `2g = F + 1`. For a numerical semigroup `S`, conversely `Φ(S) = S` iff `S` is
symmetric iff `F(S)` is its only pseudo-Frobenius number, and a symmetric `S` is almost
symmetric. -/
theorem result (U : NumericalSet) :
    (Symmetric U → phi U = members U ∧ (∀ f, PseudoFrobenius U f → f = frobenius U) ∧
      2 * U.gaps.card = frobenius U + 1) ∧
    (Semigroup U →
      (phi U = members U ↔ Symmetric U) ∧
      (Symmetric U ↔ ∀ f, PseudoFrobenius U f → f = frobenius U) ∧
      (Symmetric U → AlmostSymmetric U)) := by
  classical
  refine ⟨fun hsym => ⟨phi_of_type_one U (symmetric_type_one U hsym),
    symmetric_type_one U hsym, symmetric_genus U hsym⟩, fun hS => ?_⟩
  refine ⟨⟨fun hphi => ?_, fun hsym => phi_of_type_one U (symmetric_type_one U hsym)⟩,
    ⟨symmetric_type_one U, type_one_symmetric U hS⟩, fun hsym => ?_⟩
  · apply type_one_symmetric U hS
    have hdel : deleteRows U (retainedRows U) = U.gaps := by
      ext n
      have h := congrArg (fun T : Set ℕ => n ∈ T) hphi
      simp only [phi, members, Set.mem_ofPred_eq, eq_iff_iff] at h
      exact not_iff_not.mp h
    have hsub : retainedRows U ⊆ U.gaps := Finset.filter_subset _ _
    have hcard : U.gaps.card ≤ (retainedRows U).card := by
      rw [← hdel]
      exact Finset.card_image_le
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    intro f hf
    have hfr : f ∈ retainedRows U := heq ▸ hf.1
    rcases (Finset.mem_filter.mp hfr).2 with h | h
    · exact h
    · exact absurd hf h
  · have hg := symmetric_genus U hsym
    refine ⟨hS, ?_⟩
    have hpf : U.gaps.filter (PseudoFrobenius U) = {frobenius U} := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun h => symmetric_type_one U hsym f h.2
      · rintro rfl
        exact ⟨frob_mem U, frob_pf U⟩
    rw [hpf, Finset.card_singleton]
    exact hg

end D5.S3.Combinatorics.Partitions.DelgadoSuerYesilPhiFixedPoints
