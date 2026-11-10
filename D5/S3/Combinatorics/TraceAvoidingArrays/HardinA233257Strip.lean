/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233257Strip.finite_certificate
   digest: Closed form and generating function for the two-row antidiagonal strip. -/
/-
admission_basis: open-problem-resolution (#28792; Proved)
escape_witness: none; finite cases and transfer certificates normalize, matrix powers
  apply Mathlib's eigenvector power theorem, and two-label classification specializes
  frozen HardinA233177Ladder.two_label_classification after copying the upper row to
  four rows and recovering the lower row by finite three-label constraints.
Legal: proof_shape=bind-only; consumers=a, literal_card
decLegal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=literal_card, finite_certificate, weighted_count
Proper: proof_shape=bind-only; consumers=literal_card, proper_word, two_classification
cellOrder: proof_shape=bind-only; consumers=RowNormal, Canon, pattern_cards, weighted_count
RowNormal: proof_shape=bind-only; consumers=literal_card
Canon: proof_shape=bind-only; consumers=Patterns
literal_card: proof_shape=bind-only; consumers=weighted_count
Col: proof_shape=bind-only; consumers=step, cl, proper_word
step: proof_shape=bind-only; consumers=transfer_certificate, proper_word, proper_count
cl: proof_shape=bind-only; consumers=transfer_certificate, proper_count
T: proof_shape=bind-only; consumers=transfer_certificate, proper_count
v: proof_shape=bind-only; consumers=transfer_certificate, proper_count
transfer_certificate: proof_shape=bind-only; consumers=proper_count
proper_word: proof_shape=bind-only; consumers=proper_count
proper_count: proof_shape=bind-only; consumers=pattern_cards
finite_certificate: proof_shape=bind-only; consumers=result
used: proof_shape=bind-only; consumers=used_image, used_cases, two_classification, weighted_count
used_image: proof_shape=bind-only; consumers=used_cases, used_relabel, alt_properties, two_classification
at_least_two: proof_shape=bind-only; consumers=used_cases, pattern_cards
used_cases: proof_shape=bind-only; consumers=weighted_count
relabel: proof_shape=bind-only; consumers=pattern_cards
used_relabel: proof_shape=bind-only; consumers=pattern_cards
alt: proof_shape=bind-only; consumers=alt_properties, two_classification, two_count
alt_properties: proof_shape=bind-only; consumers=two_count
two_classification: proof_shape=bind-only; consumers=two_count
two_count: proof_shape=bind-only; consumers=pattern_cards
Patterns: proof_shape=bind-only; consumers=pattern_cards, weighted_count
pattern_cards: proof_shape=bind-only; consumers=weighted_count
weighted_count: proof_shape=bind-only; consumers=closed_form, recurrence, result
closed_form: proof_shape=bind-only; consumers=result
recurrence: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Literal normalization, canonical pair patterns and the last-column transfer. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
open D5.S3.Combinatorics.TraceAvoidingArrays
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

def Legal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) : Prop :=
  (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ∧
  (∀ (j : Fin n) (h : j.val + 1 < n),
    (∀ r : Fin 2, A (r, j) ≠ A (r, ⟨j.val + 1, h⟩) ∧
      (A (r, j)).val + (A (r, ⟨j.val + 1, h⟩)).val ≠ 5) ∧
    (A (1, j) ≠ A (0, ⟨j.val + 1, h⟩) ∧
      (A (1, j)).val + (A (0, ⟨j.val + 1, h⟩)).val ≠ 5)) ∧ HardinA233175PairStrip.normal A

private instance decLegal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) :
    Decidable (Legal A) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin 2 × Fin n → Fin 6 => Legal A)).card

attribute [local irreducible] a

private def Proper {n : ℕ} (P : Fin 2 × Fin n → Fin 3) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n),
    (∀ r : Fin 2, P (r, j) ≠ P (r, ⟨j.val + 1, h⟩)) ∧
      P (1, j) ≠ P (0, ⟨j.val + 1, h⟩)

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin 2 × Fin n) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective
private abbrev RowNormal {n : ℕ} (A : Fin 2 × Fin n → Fin 6) :=
  @HardinA233177Canonical.Normal (Fin 2 × Fin n) (cellOrder n).toLT A
private abbrev Canon {n : ℕ} (P : Fin 2 × Fin n → Fin 3) :=
  @HardinA233177Canonical.Canonical (Fin 2 × Fin n) (cellOrder n).toLT 3 P

private theorem literal_card {n : ℕ} (hn : 0 < n) :
    a n = Nat.card {A : Fin 2 × Fin n → Fin 6 //
      Proper (beta ∘ A) ∧ A (0, ⟨0, hn⟩) = 0 ∧ RowNormal A} := by
  classical
  have horder (p q : Fin 2 × Fin n) :
      @LT.lt _ (cellOrder n).toLT p q ↔
        p.1.val * n + p.2.val < q.1.val * n + q.2.val := by
    change p.2.val + n * p.1.val < q.2.val + n * q.1.val ↔ _
    simp only [Nat.add_comm, Nat.mul_comm]
  have hfirst (A : Fin 2 × Fin n → Fin 6) :
      (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ↔ A (0, ⟨0, hn⟩) = 0 := by
    constructor
    · rintro ⟨j, hj, h⟩
      simpa only [show j = ⟨0, hn⟩ from Fin.ext hj] using h
    · exact fun h => ⟨⟨0, hn⟩, rfl, h⟩
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Legal, hfirst,
    HardinA233175PairStrip.normal, RowNormal, HardinA233177Canonical.Normal, horder, Proper,
    Function.comp_apply, HardinA233251TriangleStrip.colour_bond_iff]
  tauto

private abbrev Col := Fin 3 × Fin 3
private def step (u v : Col) : Prop := u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ u.2 ≠ v.1
private def cl (_ v : Col) : Fin 2 := if v.1 = v.2 then 0 else 1
private def T : Matrix (Fin 2) (Fin 2) ℤ := !![2, 2; 1, 1]
private def v : Fin 2 → ℤ := ![12, 12]

open scoped Classical in
private theorem transfer_certificate :
    (∀ u w : Col, step u w → ∀ s,
      (∑ z : Col, if step w z ∧ True ∧ cl w z = s then (1 : ℤ) else 0) =
        T (cl u w) s) ∧
    (∀ s, (∑ u : Col, ∑ w : Col,
      if step u w ∧ cl u w = s then (1 : ℤ) else 0) = v s) := by
  constructor
  · intro u w _ s
    rcases w with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> fin_cases s <;>
      (simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]; norm_num [step, cl, T])
  · intro s
    fin_cases s <;>
      (simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]; norm_num [step, cl, v])

private theorem proper_word {n : ℕ} (P : Fin 2 × Fin n → Fin 3) :
    Proper P ↔ TransferMatrix.good step (fun _ _ _ => True)
      (List.ofFn (fun j => (P (0, j), P (1, j)))) := by
  rw [TransferMatrix.good_iff_local]
  have get (k : ℕ) (hk : k < n) :
      (List.ofFn (fun j => (P (0, j), P (1, j)))).getD k default =
        (P (0, ⟨k, hk⟩), P (1, ⟨k, hk⟩)) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
  simp only [List.length_ofFn, implies_true, and_true]
  constructor
  · intro h k hk
    have hh := h ⟨k, by omega⟩ hk
    simpa only [get k (by omega), get (k+1) hk, step, Fin.forall_fin_two, and_assoc] using hh
  · intro h j hj
    have hh := h j.val hj
    simpa only [get j.val j.isLt, get (j.val+1) hj, step, Fin.forall_fin_two, and_assoc] using hh

private theorem proper_count (n : ℕ) :
    (Nat.card {P : Fin 2 × Fin (n+2) → Fin 3 // Proper P} : ℤ) = 24 * 3 ^ n := by
  classical
  let E : {P : Fin 2 × Fin (n+2) → Fin 3 // Proper P} ≃
      {w : Fin (n+2) → Col // TransferMatrix.good step (fun _ _ _ => True) (List.ofFn w)} := {
    toFun := fun P => ⟨fun j => (P.val (0, j), P.val (1, j)), (proper_word _).mp P.property⟩
    invFun := fun w => ⟨fun p => if p.1 = 0 then (w.val p.2).1 else (w.val p.2).2, by
      apply (proper_word _).mpr
      simpa only [ite_true, show (1 : Fin 2) ≠ 0 from by decide, ite_false] using w.property⟩
    left_inv := by
      intro P
      apply Subtype.ext
      funext p
      rcases p with ⟨r, j⟩
      fin_cases r <;> rfl
    right_inv := by intro w; apply Subtype.ext; funext j; exact Prod.eta _ }
  rw [Nat.card_congr E]
  have hbridge := TransferMatrix.cardMatrix step (fun _ _ _ => True) cl T v
    (by
      intro u w hw s
      rw [← transfer_certificate.1 u w hw s]
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : step w z ∧ True ∧ cl w z = s <;> simp [h])
    (by
      intro s
      rw [← transfer_certificate.2 s]) n
  rw [hbridge]
  have hv : Module.End.HasUnifEigenvector (Matrix.toLin' T.transpose) 3 1 v := by
    constructor
    · apply Module.End.mem_genEigenspace_one.mpr
      ext i
      fin_cases i <;>
        norm_num [Matrix.toLin'_apply, T, v, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · intro h
      have hzero := congrFun h 0
      norm_num [v] at hzero
  have hpow : (T ^ n).transpose.mulVec v = (3 : ℤ) ^ n • v := by
    simpa only [← Matrix.toLin'_pow, Matrix.toLin'_apply, Matrix.transpose_pow] using
      hv.pow_apply n
  rw [← Matrix.dotProduct_transpose_mulVec, hpow]
  norm_num [dotProduct, Fin.sum_univ_two, v, Pi.smul_apply, smul_eq_mul]
  ring

/-- The empty coefficient and the one-column literal count. -/
theorem finite_certificate : a 0 = 0 ∧ a 1 = 3 := by
  constructor <;> decide +kernel

private noncomputable def used {n : ℕ} (P : Fin 2 × Fin n → Fin 3) : ℕ :=
  Nat.card (Set.range P)

private theorem used_image {n : ℕ} (P : Fin 2 × Fin n → Fin 3) :
    used P = (Finset.univ.image P).card := by
  classical
  have he : Set.range P = (↑(Finset.univ.image P) : Set (Fin 3)) := by ext x; simp
  rw [used, he, Nat.card_coe_set_eq, Set.ncard_coe_finset]

private theorem at_least_two {n : ℕ} (P : Fin 2 × Fin (n+2) → Fin 3)
    (hp : Proper P) : ∃ i j, P i ≠ P j :=
  ⟨(0, 0), (0, 1), (hp 0 (by change 0+1 < n+2; omega)).1 0⟩

private theorem used_cases {n : ℕ} (P : Fin 2 × Fin (n+2) → Fin 3)
    (hp : Proper P) : used P = 2 ∨ used P = 3 := by
  classical
  obtain ⟨i, j, hij⟩ := at_least_two P hp
  have hsub : ({P i, P j} : Finset (Fin 3)) ⊆ Finset.univ.image P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp
  have hlow := Finset.card_le_card hsub
  have hupp := Finset.card_le_univ (Finset.univ.image P)
  rw [used_image]
  simp only [Finset.card_pair hij, Fintype.card_fin] at hlow hupp
  omega

private theorem relabel {n : ℕ} (e : Equiv.Perm (Fin 3))
    (P : Fin 2 × Fin n → Fin 3) : Proper (e ∘ P) ↔ Proper P := by
  simp only [Proper, Function.comp_apply, e.injective.ne_iff]

private theorem used_relabel {n : ℕ} (e : Equiv.Perm (Fin 3))
    (P : Fin 2 × Fin n → Fin 3) : used (e ∘ P) = used P := by
  classical
  rw [used_image, used_image, ← Finset.image_image]
  exact Finset.card_image_of_injective _ e.injective

private def alt (n : ℕ) (b c : Fin 3) : Fin 2 × Fin n → Fin 3 :=
  fun p => if p.2.val % 2 = 0 then b else c

private theorem alt_properties (n : ℕ) (b c : Fin 3) (hbc : b ≠ c) :
    Proper (alt (n+2) b c) ∧ used (alt (n+2) b c) = 2 := by
  classical
  constructor
  · intro j hj
    have hpar : (j.val+1) % 2 = 0 ↔ ¬ j.val % 2 = 0 := by omega
    by_cases h : j.val % 2 = 0 <;>
      simp [alt, h, hpar, hbc, Ne.symm hbc]
  · rw [used_image]
    have he : Finset.univ.image (alt (n+2) b c) = {b, c} := by
      ext x
      constructor
      · rintro hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        simp only [alt]
        split_ifs <;> simp
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (rfl | rfl)
        · exact Finset.mem_image.mpr ⟨(0, 0), Finset.mem_univ _, rfl⟩
        · exact Finset.mem_image.mpr ⟨(0, 1), Finset.mem_univ _, rfl⟩
    rw [he, Finset.card_insert_of_notMem (by simpa using hbc), Finset.card_singleton]

private theorem two_classification {n : ℕ} (P : Fin 2 × Fin (n+2) → Fin 3)
    (hp : Proper P) (hu : used P = 2) :
    ∃ b c : Fin 3, b ≠ c ∧ P = alt (n+2) b c := by
  have missing : ∃ d : Fin 3, ∀ i, P i ≠ d := by
    by_contra h
    push Not at h
    have he : Finset.univ.image P = Finset.univ := by
      ext d
      simp only [Finset.mem_univ, iff_true]
      obtain ⟨i, hi⟩ := h d
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    rw [used_image, he] at hu
    norm_num at hu
  obtain ⟨d, hd⟩ := missing
  have unique (x y z : Fin 3) (hx : x ≠ d) (hy : y ≠ d) (hz : z ≠ d)
      (hxz : x ≠ z) (hyz : y ≠ z) : x = y := by
    apply Fin.ext
    have := x.isLt
    have := y.isLt
    have := z.isLt
    have := d.isLt
    simp only [ne_eq, Fin.ext_iff] at hx hy hz hxz hyz
    omega
  have rows (j : Fin (n+2)) : P (1, j) = P (0, j) := by
    by_cases hj : j.val + 1 < n+2
    · exact unique _ _ (P (0, ⟨j.val+1, hj⟩)) (hd _) (hd _) (hd _)
        (hp j hj).2 ((hp j hj).1 0)
    · have hk : j.val - 1 < n+2 := by omega
      have hkn : (j.val - 1) + 1 < n+2 := by omega
      have he : (⟨j.val - 1 + 1, hkn⟩ : Fin (n+2)) = j := by
        apply Fin.ext
        change j.val - 1 + 1 = j.val
        have := j.isLt
        omega
      have hh := hp ⟨j.val-1, hk⟩ hkn
      rw [he] at hh
      exact unique _ _ (P (1, ⟨j.val-1, hk⟩)) (hd _) (hd _) (hd _)
        (Ne.symm (hh.1 1)) (Ne.symm hh.2)
  let Q : Fin 4 × Fin (n+2) → Fin 3 := fun p => P (0, p.2)
  have hQ : HardinA233177PairTransfer.Proper Q := by
    intro j hj r s _
    exact (hp j hj).1 0
  obtain ⟨b, c, hbc, hQalt⟩ := HardinA233177Ladder.two_label_classification
    (by omega) Q hQ d (fun p => hd (0, p.2))
  have row (j : Fin (n+2)) : P (0, j) = alt (n+2) b c (0, j) :=
    congrFun hQalt (0, j)
  refine ⟨b, c, hbc, ?_⟩
  funext p
  rcases p with ⟨r, j⟩
  fin_cases r
  · exact row j
  · exact (rows j).trans (row j)

private theorem two_count (n : ℕ) :
    Nat.card {P : Fin 2 × Fin (n+2) → Fin 3 // Proper P ∧ used P = 2} = 6 := by
  let E : {bc : Fin 3 × Fin 3 // bc.1 ≠ bc.2} →
      {P : Fin 2 × Fin (n+2) → Fin 3 // Proper P ∧ used P = 2} :=
    fun bc => ⟨alt (n+2) bc.val.1 bc.val.2, alt_properties n _ _ bc.property⟩
  have hE : Function.Bijective E := by
    constructor
    · intro bc de he
      have heq := congrArg Subtype.val he
      apply Subtype.ext
      apply Prod.ext
      · exact congrFun heq (0, 0)
      · exact congrFun heq (0, 1)
    · intro P
      obtain ⟨b, c, hbc, he⟩ := two_classification P.val P.property.1 P.property.2
      exact ⟨⟨(b,c), hbc⟩, Subtype.ext he.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective E hE)]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private abbrev Patterns (n : ℕ) :=
  {P : Fin 2 × Fin n → Fin 3 // Proper P ∧ Canon P}

private theorem pattern_cards (n : ℕ) :
    Nat.card (Patterns (n+2)) = 4 * 3 ^ n ∧
      Nat.card {P : Patterns (n+2) // used P.val = 2} = 1 := by
  classical
  have h := @HardinA233177Canonical.canonical_pattern_card (Fin 2 × Fin (n+2))
    inferInstance (cellOrder _) Proper relabel at_least_two
  have hcount := proper_count n
  have hi : (Nat.card (Patterns (n+2)) : ℤ) = 4 * 3 ^ n := by
    rw [h] at hcount
    push_cast at hcount
    linarith
  constructor
  · exact_mod_cast hi
  · let S : (Fin 2 × Fin (n+2) → Fin 3) → Prop := fun P => Proper P ∧ used P = 2
    have hS : ∀ e : Equiv.Perm (Fin 3), ∀ P, S (e ∘ P) ↔ S P := by
      intro e P
      simp only [S, relabel, used_relabel]
    have ht := @HardinA233177Canonical.canonical_pattern_card (Fin 2 × Fin (n+2))
      inferInstance (cellOrder _) S hS (fun P hP => at_least_two P hP.1)
    rw [two_count] at ht
    have E : {P // S P ∧ Canon P} ≃ {P : Patterns (n+2) // used P.val = 2} := {
      toFun := fun P => ⟨⟨P.val, P.property.1.1, P.property.2⟩, P.property.1.2⟩
      invFun := fun P => ⟨P.val.val, ⟨P.val.property.1, P.property⟩, P.val.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr E] at ht
    omega

private theorem weighted_count (n : ℕ) :
    a (n+2) = 2 ^ (2*n+1) * (4 * 3 ^ n + 1) := by
  classical
  let z : Fin 2 × Fin (n+2) := (0, ⟨0, by omega⟩)
  have hz : ∀ i, @LE.le _ (cellOrder (n+2)).toLE z i := by
    intro i
    change 0 ≤ i.2.val + (n+2) * i.1.val
    omega
  have hs := @HardinA233177Canonical.normalized_card (Fin 2 × Fin (n+2))
    inferInstance (cellOrder _) z hz Proper
  have hsum : a (n+2) = ∑ P : Patterns (n+2), 2 ^ (2*n+4 - used P.val) := by
    rw [literal_card (by omega)]
    simp only [Fintype.card_prod, Fintype.card_fin] at hs
    refine hs.trans ?_
    apply Finset.sum_congr
    · ext P
      simp only [Finset.mem_univ]
    · intro P _
      congr 1
  have summand (P : Patterns (n+2)) :
      2 ^ (2*n+4-used P.val) = 2 ^ (2*n+1) +
        2 ^ (2*n+1) * (if used P.val = 2 then 1 else 0) := by
    rcases used_cases P.val P.property.1 with hu | hu
    · rw [hu]
      simp only [ite_true]
      have he : 2*n+4-2 = (2*n+1)+1 := by omega
      rw [he, pow_succ]
      ring
    · rw [hu]
      simp only [show (3 : ℕ) ≠ 2 from by decide, ite_false, mul_zero, add_zero]
      congr 1
  have hc : (∑ P : Patterns (n+2), if used P.val = 2 then (1 : ℕ) else 0) = 1 := by
    simp only [Finset.sum_boole, Nat.cast_id]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using (pattern_cards n).2
  rw [hsum]
  simp_rw [summand]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card, (pattern_cards n).1]
  ring

/-- Barker's closed form with the lower index shifted to two. -/
theorem closed_form (n : ℕ) :
    9 * a (n+2) = 2 ^ (2*n+1) * (4 * 3 ^ (n+2) + 9) := by
  rw [weighted_count, pow_add]
  norm_num
  ring

/-- Hardin's recurrence, interpreted in the integers. -/
theorem recurrence (n : ℕ) :
    (a (n+4) : ℤ) = 16 * (a (n+3) : ℤ) - 48 * (a (n+2) : ℤ) := by
  have hh : ∀ m, (a (m+2) : ℤ) = (2 : ℤ) ^ (2*m+1) * (4 * (3 : ℤ)^m + 1) :=
    fun m => by exact_mod_cast weighted_count m
  rw [show n+4 = (n+2)+2 from by omega, hh,
    show n+3 = (n+1)+2 from by omega, hh, hh]
  simp only [show 2*(n+2)+1 = (2*n+1)+4 from by omega,
    show 2*(n+1)+1 = (2*n+1)+2 from by omega, pow_succ]
  ring

open PowerSeries in
/-- The literal generating series, closed form and recurrence in one settling statement. -/
theorem result :
    ((1 - 4 * X) * (1 - 12 * X) * (PowerSeries.mk fun n => (a n : ℤ)) =
      X * (3 - 38 * X + 88 * X ^ 2)) ∧
    (∀ n : ℕ, 9 * a (n+2) = 2 ^ (2*n+1) * (4 * 3 ^ (n+2) + 9)) ∧
    (∀ n : ℕ, (a (n+4) : ℤ) = 16 * (a (n+3) : ℤ) - 48 * (a (n+2) : ℤ)) := by
  refine ⟨?_, closed_form, recurrence⟩
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1-4*X)*(1-12*X)*F = F - 16*(F*X^1) + 48*(F*X^2) := by ring
  have hr : (X*(3-38*X+88*X^2) : PowerSeries ℤ) = 3*X-38*X^2+88*X^3 := by ring
  change (1-4*X)*(1-12*X)*F = _
  rw [hp, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow, F, coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega)]
    have hh := recurrence (n-4)
    rw [show n-4+4 = n from by omega, show n-4+3 = n-1 from by omega,
      show n-4+2 = n-2 from by omega] at hh
    linarith
  · have h2 : a 2 = 10 := by simpa using weighted_count 0
    have h3 : a 3 = 104 := by simpa using weighted_count 1
    have h0 := finite_certificate.1
    have h1 := finite_certificate.2
    interval_cases n <;> norm_num [h0, h1, h2, h3]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233257Strip
