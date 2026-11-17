/- GID: D5/S3/ConceptDynamics/DependencyTopology/FiniteSupportPatternRealization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DependencyTopology/FiniteSupportPatternRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Accessible finite union families have exact decidable propositional proof kernels. -/

import D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet
import D5.S3.ConceptDynamics.DagSemantics.StrictDependencyCoordinate
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.DeriveCountable

/-! Exact finite support realization with ordinary propositional syntax and actual certificates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DependencyTopology.FiniteSupportPatternRealization

open LegalLedgerFixedSet SupportFamilyNotIntersectionClosed
open DagSemantics.StrictDependencyCoordinate

/-- Ordinary finite propositional syntax over countably many variables. -/
inductive Formula where
  | atom : Nat → Formula
  | bottom : Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq, Countable

/-- Truth under an ordinary Boolean valuation. -/
def Formula.eval (v : Nat → Bool) : Formula → Bool
  | .atom i => v i
  | .bottom => false
  | .imp p q => !(p.eval v) || q.eval v

/-- Syntactic negation, with the usual truth table. -/
def Formula.neg (p : Formula) : Formula := .imp p .bottom

/-- The index of the left variable of a tautology; other syntax is irrelevant to ranks. -/
private def Formula.index : Formula → Nat
  | .imp (.atom i) _ => i
  | _ => 0

/-- Distinct variables yield distinct syntactic tautologies. -/
def e {n : Nat} (x : Fin n) : Formula := .imp (.atom x.val) (.atom x.val)

private theorem e_injective {n : Nat} : Function.Injective (@e n) := by
  intro x y h
  simp only [e, Formula.imp.injEq, Formula.atom.injEq, and_self] at h
  exact Fin.ext h

/-- The three finite support laws, with no requirement that every element occur. -/
def Pattern {n : Nat} (F : Finset (Finset (Fin n))) : Prop :=
  ∅ ∈ F ∧
  (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) ∧
  (∀ A ∈ F, A.Nonempty → ∃ x ∈ A, A.erase x ∈ F)

/-- Only legal pairs are proof symbols. Membership is decided by the finite table. -/
def Legal {n : Nat} (F : Finset (Finset (Fin n))) (p : Finset (Fin n) × Fin n) : Prop :=
  p.1 ∈ F ∧ p.2 ∉ p.1 ∧ insert p.2 p.1 ∈ F

instance {n : Nat} (F : Finset (Finset (Fin n))) (p : Finset (Fin n) × Fin n) :
    Decidable (Legal F p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Exactly one dummy symbol, `none`, accompanies the legal symbols. -/
abbrev ProofSymbol {n : Nat} (F : Finset (Finset (Fin n))) := Option {p // Legal F p}

/-- The actual executable acceptance function and readouts of the pattern kernel. -/
def kernel {n : Nat} (F : Finset (Finset (Fin n))) :
    KernelData Formula (ProofSymbol F) Unit (Nat → Bool) :=
  (fun π p => match π with
    | none => false
    | some t => decide (Legal F t.val ∧ p = e t.val.2),
   fun _ => ∅,
   fun π => match π with
    | none => ∅
    | some t => t.val.1.image e,
   ∅, Formula.neg, fun _ _ => True, fun v p => p.eval v = true)

/-- Simultaneous selected legal proofs and bounded ranks for every feasible support. -/
private theorem ranked_witnesses {n : Nat} (F : Finset (Finset (Fin n)))
    (hF : Pattern F) (A : Finset (Fin n)) (hA : A ∈ F) :
    ∃ (w : Fin n → ProofSymbol F) (r : Nat → Nat),
      ∀ x ∈ A,
        (kernel F).accept (w x) (e x) = true ∧
        (kernel F).refs (w x) ⊆ A.image e ∧
        (∀ q ∈ (kernel F).refs (w x), r q.index < r x.val) ∧
        r x.val < A.card := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hn : A.Nonempty
    · obtain ⟨x, hx, hB⟩ := hF.2.2 A hA hn
      let B := A.erase x
      change B ∈ F at hB
      have hBA : B ⊂ A := Finset.erase_ssubset hx
      obtain ⟨w, r, hw⟩ := ih B hBA hB
      have hxB : x ∉ B := Finset.notMem_erase x A
      have hins : insert x B = A := Finset.insert_erase hx
      let π : ProofSymbol F := some ⟨(B, x), hB, hxB, hins ▸ hA⟩
      let w' : Fin n → ProofSymbol F := fun y => if y = x then π else w y
      let r' : Nat → Nat := fun i => if i = x.val then B.card else r i
      have hidx : ∀ q ∈ B.image e, q.index ≠ x.val := by
        intro q hq
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
        change y.val ≠ x.val
        intro he
        exact hxB (Fin.ext he ▸ hy)
      have hcard : B.card < A.card := Finset.card_erase_lt_of_mem hx
      refine ⟨w', r', ?_⟩
      intro y hy
      by_cases hyx : y = x
      · subst y
        have href : (kernel F).refs (w' x) = B.image e := by simp [w', π, kernel, KernelData.refs]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [w', π, kernel, KernelData.accept, Legal, hB, hxB, hins, hA]
        · rw [href]
          exact Finset.image_subset_image (Finset.erase_subset x A)
        · intro q hq
          rw [href] at hq
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
          have hzx : z.val ≠ x.val := hidx (e z) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
          simpa [r', Formula.index, e, hzx] using (hw z hz).2.2.2
        · simpa [r'] using hcard
      · have hyB : y ∈ B := Finset.mem_erase.mpr ⟨hyx, hy⟩
        have hyval : y.val ≠ x.val := fun h => hyx (Fin.ext h)
        have hwy : w' y = w y := if_neg hyx
        refine ⟨hwy ▸ (hw y hyB).1, ?_, ?_, ?_⟩
        · rw [hwy]
          exact (hw y hyB).2.1.trans (Finset.image_subset_image (Finset.erase_subset x A))
        · intro q hq
          rw [hwy] at hq
          have hqx := hidx q ((hw y hyB).2.1 hq)
          simpa [r', hqx, hyval] using (hw y hyB).2.2.1 q hq
        · exact (by simpa [r', hyval] using lt_trans (hw y hyB).2.2.2 hcard)
    · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst A
      exact ⟨fun _ => none, fun _ => 0, by simp⟩

/-- The selected references, rather than a common graph of all proofs, form the certificate. -/
private theorem feasible_certificate {n : Nat} (F : Finset (Finset (Fin n)))
    (hF : Pattern F) (A : Finset (Fin n)) (hA : A ∈ F) :
    ∃ C : CertifiedNodes (kernel F), C.nodes = A.image e := by
  classical
  obtain ⟨w, r, hw⟩ := ranked_witnesses F hF A hA
  let pick : {p // p ∈ A.image e} → Fin n := fun p =>
    (Finset.mem_image.mp p.property).choose
  have hpick : ∀ p, pick p ∈ A ∧ e (pick p) = p.val := fun p =>
    (Finset.mem_image.mp p.property).choose_spec
  let W : {p // p ∈ A.image e} → ProofSymbol F := fun p => w (pick p)
  refine ⟨⟨⟨A.image e, W⟩, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro p
    simpa only [W, ← (hpick p).2] using (hw (pick p) (hpick p).1).1
  · intro p a ha
    exact Finset.notMem_empty a ha
  · intro p q hq
    exact (hw (pick p) (hpick p).1).2.1 hq
  · apply acyclic_of_strictCoordinate (coordinate := fun p : Formula => r p.index)
    rintro q p ⟨hp, hq⟩
    have h := (hw (pick ⟨p, hp⟩) (hpick ⟨p, hp⟩).1).2.2.1 q hq
    have he := (hpick ⟨p, hp⟩).2
    change e (pick ⟨p, hp⟩) = p at he
    change r q.index < r p.index
    rw [← he]
    exact h

/-- Every actual certified support is the image of a member of the finite family. -/
private theorem certificate_feasible {n : Nat} (F : Finset (Finset (Fin n)))
    (hF : Pattern F) (C : CertifiedNodes (kernel F)) :
    ∃ A ∈ F, C.nodes = A.image e := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun x => e x ∈ C.nodes)
  have hA : ∀ x, x ∈ A ↔ e x ∈ C.nodes := by simp [A]
  have hnodes : C.nodes = A.image e := by
    ext p
    constructor
    · intro hp
      have ha : (kernel F).accept (C.witness ⟨p, hp⟩) p = true := C.property.1 ⟨p, hp⟩
      cases he : C.witness ⟨p, hp⟩ with
      | none => rw [he] at ha; simp [kernel, KernelData.accept] at ha
      | some t =>
        have heq : p = e t.val.2 := by
          rw [he] at ha
          exact (of_decide_eq_true ha).2
        exact Finset.mem_image.mpr ⟨t.val.2, (hA _).mpr (heq ▸ hp), heq.symm⟩
    · rintro hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact (hA x).mp hx
  have local_piece : ∀ x ∈ A, ∃ T ∈ F, x ∈ T ∧ T ⊆ A := by
    intro x hx
    have hxe := (hA x).mp hx
    let π := C.witness ⟨e x, hxe⟩
    have ha : (kernel F).accept π (e x) = true := C.property.1 ⟨e x, hxe⟩
    cases he : π with
    | none => simp [he, kernel, KernelData.accept] at ha
    | some t =>
      have hacc : Legal F t.val ∧ e x = e t.val.2 := by
        apply of_decide_eq_true
        simpa only [he, kernel, KernelData.accept] using ha
      have hxx : x = t.val.2 := e_injective hacc.2
      refine ⟨insert t.val.2 t.val.1, t.property.2.2, ?_, ?_⟩
      · simp [hxx]
      · intro y hy
        rcases Finset.mem_insert.mp hy with hy | hy
        · exact hy ▸ hxx ▸ hx
        · apply (hA y).mpr
          apply C.property.2.2.1 ⟨e x, hxe⟩ (e y)
          change e y ∈ (kernel F).refs π
          simp only [he, kernel, KernelData.refs]
          exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  choose T hT using local_piece
  let U : Finset (Fin n) := A.attach.sup (fun x => T x.val x.property)
  have hUF : U ∈ F := Finset.sup_mem (↑F : Set (Finset (Fin n))) hF.1 hF.2.1
    A.attach (fun x => T x.val x.property) (fun x _ => (hT x.val x.property).1)
  have hUA : U = A := by
    apply Finset.Subset.antisymm
    · exact Finset.sup_le (fun x _ => (hT x.val x.property).2.2)
    · intro x hx
      exact (Finset.le_sup (f := fun x : {x // x ∈ A} => T x.val x.property)
        (Finset.mem_attach A ⟨x, hx⟩)) (hT x hx).2.1
  exact ⟨A, hUA ▸ hUF, hnodes⟩

/-- Every finite enumerated accessible union family is realized by this precise pattern kernel. -/
theorem finite_support_pattern_realization {n : Nat} (F : Finset (Finset (Fin n)))
    (hF : Pattern F) :
    SourceLaws (kernel F) ∧
      supportFamily (kernel F) = {Y | ∃ A ∈ F, Y = (↑(A.image e) : Set Formula)} := by
  have sound : ∀ p, Proved (kernel F) p → ∀ v, (kernel F).holds v p := by
    rintro p ⟨π, hπ, _⟩ v
    cases π with
    | none => simp [kernel, KernelData.accept] at hπ
    | some t =>
      have hp : p = e t.val.2 := (of_decide_eq_true hπ).2
      subst p
      change (!(v t.val.2.val) || v t.val.2.val) = true
      cases v t.val.2.val <;> rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp v _
    exact sound p hp v
  · rintro p ⟨π, hπ, _⟩
    cases π with
    | none => simp [kernel, KernelData.accept] at hπ
    | some t =>
      have hp : p = e t.val.2 := (of_decide_eq_true hπ).2
      obtain ⟨C, hC⟩ := feasible_certificate F hF (insert t.val.2 t.val.1) t.property.2.2
      refine ⟨⟨C, ?_⟩⟩
      rw [hC, hp]
      exact Finset.mem_image.mpr ⟨t.val.2, Finset.mem_insert_self _ _, rfl⟩
  · rintro p ⟨hp, hn⟩
    have ht := sound p hp (fun _ => false)
    have hf := sound ((kernel F).neg p) hn (fun _ => false)
    change p.eval (fun _ => false) = true at ht
    change (!(p.eval (fun _ => false)) || false) = true at hf
    simp [ht] at hf
  · ext Y
    constructor
    · rintro ⟨C, hC⟩
      obtain ⟨A, hA, he⟩ := certificate_feasible F hF C
      exact ⟨A, hA, hC.symm.trans (congrArg (fun s : Finset Formula => (↑s : Set Formula)) he)⟩
    · rintro ⟨A, hA, rfl⟩
      obtain ⟨C, hC⟩ := feasible_certificate F hF A hA
      exact ⟨C, congrArg (fun s : Finset Formula => (↑s : Set Formula)) hC⟩

#print axioms finite_support_pattern_realization

end D5.S3.ConceptDynamics.DependencyTopology.FiniteSupportPatternRealization
