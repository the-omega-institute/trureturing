/- GID: D5/S3/Quantum/Entanglement/Marginals/LocalMarginalRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/LocalMarginalRank
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The rank of a family of binary partial traces counts legal pairs covered by its regions. -/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRank

open scoped BigOperators
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : Type*} [Field K]

abbrev WordPair (V : Type*) := Finset V × Finset V
abbrev LegalPair (allowed : Finset V → Prop) :=
  {p : WordPair V // allowed p.1 ∧ allowed p.2}

def occupied (p : WordPair V) : Finset V := p.1 ∪ p.2

private def cut (s : Finset V) (p : WordPair V) : WordPair V := (p.1 ∩ s, p.2 ∩ s)

private def agreesOutside (s : Finset V) (p : WordPair V) : Prop := p.1 \ s = p.2 \ s

private def contributes (s : Finset V) (p q : WordPair V) : Prop :=
  cut s q = p ∧ agreesOutside s q

omit [Fintype V] in
private theorem cut_self (p : WordPair V) : cut (occupied p) p = p := by
  exact Prod.ext (Finset.inter_eq_left.mpr Finset.subset_union_left)
    (Finset.inter_eq_left.mpr Finset.subset_union_right)

omit [Fintype V] in
private theorem contributes_self (p : WordPair V) : contributes (occupied p) p p := by
  refine ⟨cut_self p, ?_⟩
  exact (Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_left).trans
    (Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_right).symm

omit [Fintype V] in
private theorem occupied_cut (s : Finset V) (q : WordPair V) :
    occupied (cut s q) = occupied q ∩ s := by
  ext i
  simp [occupied, cut, or_and_right]

omit [Fintype V] in
private theorem contributes_strict {p q : WordPair V} (h : contributes (occupied p) p q) (hne : p ≠ q) :
    (occupied p).card < (occupied q).card := by
  have hu := congrArg occupied h.1
  rw [occupied_cut] at hu
  have sub : occupied p ⊆ occupied q := by
    rw [← hu]
    exact Finset.inter_subset_left
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨sub, ?_⟩
  intro eq
  apply hne
  have hq : cut (occupied p) q = q := eq ▸ cut_self q
  exact h.1.symm.trans hq

private noncomputable def read {allowed : Finset V → Prop} (s : Finset V) (p : WordPair V)
    (f : LegalPair allowed → K) : K :=
  ∑ q : LegalPair allowed, if contributes s p q.1 then f q else 0

private noncomputable def zeta {allowed : Finset V → Prop} :
    (LegalPair allowed → K) →ₗ[K] (LegalPair allowed → K) where
  toFun f p := read (occupied p.1) p.1 f
  map_add' f g := by
    funext p
    simp only [read, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    split <;> simp_all
  map_smul' c f := by
    funext p
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, read, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    split <;> simp_all

private theorem zeta_injective {allowed : Finset V → Prop} :
    Function.Injective (zeta (K := K) (allowed := allowed)) := by
  intro f g h
  have aux : ∀ n : ℕ, ∀ p : LegalPair allowed, n + (occupied p.1).card = Fintype.card V →
      f p = g p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hrank
      have eq := congrFun h p
      change read _ _ f = read _ _ g at eq
      unfold read at eq
      rw [← Finset.add_sum_erase (s := Finset.univ) _ (Finset.mem_univ p),
          ← Finset.add_sum_erase (s := Finset.univ) _ (Finset.mem_univ p),
          ite_eq_left (contributes_self p.1), ite_eq_left (contributes_self p.1)] at eq
      have rest :
          ∑ q ∈ Finset.univ.erase p, (if contributes (occupied p.1) p.1 q.1 then f q else 0) =
          ∑ q ∈ Finset.univ.erase p, (if contributes (occupied p.1) p.1 q.1 then g q else 0) := by
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hc : contributes (occupied p.1) p.1 q.1
        · rw [ite_eq_left hc, ite_eq_left hc]
          have hlt := contributes_strict hc (fun e => (Finset.ne_of_mem_erase hq) (Subtype.ext e.symm))
          have hle : (occupied q.1).card ≤ Fintype.card V := Finset.card_le_univ _
          exact ih (Fintype.card V - (occupied q.1).card) (by omega) q (by omega)
        · simp [hc]
      rw [rest] at eq
      exact add_right_cancel eq
  funext p
  have hle : (occupied p.1).card ≤ Fintype.card V := Finset.card_le_univ _
  exact aux (Fintype.card V - (occupied p.1).card) p (by omega)


/-- Clearing occupied sites preserves legality. -/
def DownwardClosed (allowed : Finset V → Prop) : Prop :=
  ∀ ⦃x y : Finset V⦄, x ⊆ y → allowed y → allowed x

omit [Fintype V] in
private theorem contributes_union_subset {p q : WordPair V} (h : contributes (occupied p) p q) :
    occupied p ⊆ occupied q := by
  have eq := congrArg occupied h.1
  rw [occupied_cut] at eq
  rw [← eq]
  exact Finset.inter_subset_left

omit [Fintype V] in
private theorem cut_nested {a b : Finset V} (h : a ⊆ b) (q : WordPair V) :
    cut a (cut b q) = cut a q := by
  apply Prod.ext
  · exact (Finset.inter_assoc q.1 b a).trans (congrArg (q.1 ∩ ·) (Finset.inter_eq_right.mpr h))
  · exact (Finset.inter_assoc q.2 b a).trans (congrArg (q.2 ∩ ·) (Finset.inter_eq_right.mpr h))

omit [Fintype V] in
private theorem outside_cut_iff {a b : Finset V} (h : a ⊆ b) (q : WordPair V) :
    (agreesOutside a (cut b q) ∧ agreesOutside b q) ↔ agreesOutside a q := by
  simp only [agreesOutside, cut, Finset.ext_iff, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨h₁, h₂⟩ i
    by_cases hi : i ∈ b
    · simpa only [hi, and_true] using h₁ i
    · have hj : i ∉ a := fun ha => hi (h ha)
      simp only [hj, not_false_eq_true, and_true]
      simpa only [hi, not_false_eq_true, and_true] using h₂ i
  · intro hq
    constructor <;> intro i
    · by_cases hi : i ∈ a
      · simp [hi]
      · have he : i ∈ q.1 ↔ i ∈ q.2 := by simpa [hi] using hq i
        simp only [he]
    · by_cases hi : i ∈ b
      · simp [hi]
      · have hj : i ∉ a := fun ha => hi (h ha)
        simpa [hi, hj] using hq i

omit [Fintype V] in
private theorem contributes_cut {p q : WordPair V} {s : Finset V} (h : occupied p ⊆ s) :
    (contributes (occupied p) p (cut s q) ∧ agreesOutside s q) ↔
      contributes (occupied p) p q := by
  simp only [contributes, cut_nested h, and_assoc, outside_cut_iff h]

private def legalCut {allowed : Finset V → Prop} (h : DownwardClosed allowed)
    (s : Finset V) (q : LegalPair allowed) : LegalPair allowed :=
  ⟨cut s q.1, h Finset.inter_subset_left q.2.1, h Finset.inter_subset_left q.2.2⟩

private noncomputable def traceOn {allowed : Finset V → Prop} (s : Finset V)
    (f : LegalPair allowed → K) (p : LegalPair allowed) : K :=
  read s p.1 f

private theorem zeta_traceOn {allowed : Finset V → Prop} (h : DownwardClosed allowed)
    (s : Finset V) (f : LegalPair allowed → K) (p : LegalPair allowed) :
    zeta (traceOn s f) p = if occupied p.1 ⊆ s then zeta f p else 0 := by
  classical
  by_cases hps : occupied p.1 ⊆ s
  · rw [ite_eq_left hps]
    change read (occupied p.1) p.1 (traceOn s f) = read (occupied p.1) p.1 f
    unfold read traceOn
    calc
      _ = ∑ r : LegalPair allowed, ∑ q : LegalPair allowed,
          if contributes (occupied p.1) p.1 r.1 ∧ contributes s r.1 q.1 then f q else 0 := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hc : contributes (occupied p.1) p.1 r.1 <;> simp [hc, read]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _
        let r := legalCut h s q
        rw [Finset.sum_eq_single r]
        · have hr : cut s q.1 = r.1 := rfl
          have hc : contributes s r.1 q.1 ↔ agreesOutside s q.1 := by
            simp [contributes, hr]
          simp only [hc]
          exact if_congr (contributes_cut hps) rfl rfl
        · intro other _ hne
          have hg : cut s q.1 ≠ other.1 := fun he => hne (Subtype.ext he.symm)
          simp [contributes, hg]
        · intro h
          exact (h (Finset.mem_univ r)).elim
  · rw [ite_eq_right hps]
    change read (occupied p.1) p.1 (traceOn s f) = 0
    apply Finset.sum_eq_zero
    intro r _
    by_cases hpr : contributes (occupied p.1) p.1 r.1
    · rw [ite_eq_left hpr]
      apply Finset.sum_eq_zero
      intro q _
      have hc : ¬ contributes s r.1 q.1 := by
        intro he
        have sub : occupied r.1 ⊆ s := by
          rw [← he.1, occupied_cut]
          exact Finset.inter_subset_right
        exact hps ((contributes_union_subset hpr).trans sub)
      simp [hc]
    · simp [hpr]


/-- A pair is covered when its occupied sites lie in one measured region. -/
def Covered (observed : Set (Finset V)) (p : WordPair V) : Prop :=
  ∃ s ∈ observed, occupied p ⊆ s

/-- Collect the partial traces over the complements of the measured regions.
The matrix entries are indexed by legal pairs. Entries outside a region are zero. -/
noncomputable def marginalMap {allowed : Finset V → Prop} (observed : Set (Finset V)) :
    (LegalPair allowed → K) →ₗ[K] ({s // s ∈ observed} → LegalPair allowed → K) where
  toFun f s := traceOn s.1 f
  map_add' f g := by
    funext s p
    simp only [traceOn, read, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    split <;> simp_all
  map_smul' c f := by
    funext s p
    simp only [RingHom.id_apply, traceOn, read, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    split <;> simp_all

private noncomputable def coveredMap {allowed : Finset V → Prop} (observed : Set (Finset V)) :
    (LegalPair allowed → K) →ₗ[K] ({p : LegalPair allowed // Covered observed p.1} → K) where
  toFun f p := zeta f p.1
  map_add' f g := by
    funext p
    change zeta (f + g) p.1 = zeta f p.1 + zeta g p.1
    rw [map_add]
    rfl
  map_smul' c f := by
    funext p
    change zeta (c • f) p.1 = c • zeta f p.1
    rw [map_smul]
    rfl

private lemma coveredMap_surj {allowed : Finset V → Prop} (observed : Set (Finset V)) :
    Function.Surjective (coveredMap (allowed := allowed) (K := K) observed) := by
  classical
  have hz : Function.Surjective (zeta (allowed := allowed) (K := K)) :=
    LinearMap.surjective_of_injective zeta_injective
  intro data
  let lift (p : LegalPair allowed) : K :=
    if hp : Covered observed p.1 then data ⟨p, hp⟩ else 0
  obtain ⟨f, hf⟩ := hz lift
  refine ⟨f, ?_⟩
  funext p
  change zeta f p.1 = data p
  rw [hf]
  simp [lift, p.2]

private lemma ker_marginalMap {allowed : Finset V → Prop} (h : DownwardClosed allowed)
    (observed : Set (Finset V)) :
    (marginalMap (allowed := allowed) (K := K) observed).ker = (coveredMap observed).ker := by
  ext f
  simp only [LinearMap.mem_ker]
  constructor
  · intro hf
    funext p
    obtain ⟨s, hs, hc⟩ := p.2
    have hzero := congrFun hf (⟨s, hs⟩ : {s // s ∈ observed})
    change traceOn s f = 0 at hzero
    change zeta f p.1 = 0
    have hw := zeta_traceOn h s f p.1
    rw [ite_eq_left hc, hzero, map_zero] at hw
    exact hw.symm
  · intro hf
    funext s
    change traceOn s.1 f = 0
    apply zeta_injective (K := K)
    rw [map_zero]
    funext p
    rw [zeta_traceOn h s.1 f p]
    by_cases hp : occupied p.1 ⊆ s.1
    · exact (ite_eq_left hp).trans (congrFun hf ⟨p, ⟨s.1, s.2, hp⟩⟩)
    · exact ite_eq_right hp

/-- The rank of the collected partial traces counts the covered ordered legal pairs. -/
theorem finrank_marginalMap {allowed : Finset V → Prop} (h : DownwardClosed allowed)
    (observed : Set (Finset V)) :
    Module.finrank K (marginalMap (allowed := allowed) (K := K) observed).range =
      Nat.card {p : LegalPair allowed // Covered observed p.1} := by
  classical
  let L := marginalMap (allowed := allowed) (K := K) observed
  let C := coveredMap (allowed := allowed) (K := K) observed
  have hker : L.ker = C.ker := ker_marginalMap h observed
  have hr : Module.finrank K L.range = Module.finrank K C.range := by
    have hL := L.finrank_range_add_finrank_ker
    have hC := C.finrank_range_add_finrank_ker
    rw [hker] at hL
    exact Nat.add_right_cancel (hL.trans hC.symm)
  have hsurj : C.range = ⊤ := LinearMap.range_eq_top.mpr (coveredMap_surj observed)
  let : Fintype {p : LegalPair allowed // Covered observed p.1} := Fintype.ofFinite _
  rw [hr, hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRank
