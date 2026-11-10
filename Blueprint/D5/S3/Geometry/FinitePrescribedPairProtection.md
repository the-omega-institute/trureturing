# FinitePrescribedPairProtection

## Abstract

A forward scan of native pairs constructs protected replay and an original-order standalone core collapse.

**Definition 1.1 (simplices).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.simplices`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.simplices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.simplices

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def simplices (H : Finset (Finset V)) : PreAbstractSimplicialComplex V where

  faces := {s | s.Nonempty ∧ ∃ q ∈ H, s ⊆ q}

  isRelLowerSet_faces := by

    rintro s ⟨hs,q,hq,hsq⟩

    exact ⟨hs,fun t hts ht => ⟨ht,q,hq,hts.trans hsq⟩⟩

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.2 (mem_simplices).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.mem_simplices`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.mem_simplices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.mem_simplices

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

@[simp] theorem mem_simplices (H : Finset (Finset V)) (s : Finset V) :

    s ∈ simplices H ↔ s.Nonempty ∧ ∃ q ∈ H, s ⊆ q := Iff.rfl

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.3 (simplices_empty).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.simplices_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.simplices_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.simplices_empty

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

@[simp] theorem simplices_empty : simplices (∅ : Finset (Finset V)) = ⊥ := by

  apply SetLike.coe_injective

  ext s

  change (s.Nonempty ∧ ∃ q ∈ (∅ : Finset (Finset V)), s ⊆ q) ↔ False

  simp

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.4 (simplices_union).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.simplices_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.simplices_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.simplices_union

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

@[simp] theorem simplices_union (H J : Finset (Finset V)) :

    simplices (H ∪ J) = simplices H ⊔ simplices J := by

  apply SetLike.coe_injective

  ext s

  change (s.Nonempty ∧ ∃ q ∈ H ∪ J, s ⊆ q) ↔

    (s.Nonempty ∧ ∃ q ∈ H, s ⊆ q) ∨ (s.Nonempty ∧ ∃ q ∈ J, s ⊆ q)

  simp only [Finset.mem_union]

  aesop

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.5 (blocked).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.blocked`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.blocked` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.blocked

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def blocked (H : Finset (Finset V)) (P : CollapsePair V) : Prop :=

  ∃ q ∈ H, P.lower ⊆ q

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.6 (skipped).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.skipped`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.skipped` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.skipped

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def skipped : List (CollapsePair V) → Finset (Finset V) → List (CollapsePair V)

  | [], _ => []

  | P :: ps, H => if blocked H P then P :: skipped ps (insert P.upper H)

      else skipped ps H

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.7 (emitted).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.emitted`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.emitted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.emitted

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def emitted : List (CollapsePair V) → Finset (Finset V) → List (CollapsePair V)

  | [], _ => []

  | P :: ps, H => if blocked H P then emitted ps (insert P.upper H)

      else P :: emitted ps H

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.8 (advance).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.advance`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.advance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.advance

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def advance : List (CollapsePair V) → Finset (Finset V) → Finset (Finset V)

  | [], H => H

  | P :: ps, H => advance ps (if blocked H P then insert P.upper H else H)

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.9 (skippedTops).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.skippedTops`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.skippedTops` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.skippedTops

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def skippedTops (ps : List (CollapsePair V)) (H : Finset (Finset V)) :

    Finset (Finset V) := ((skipped ps H).map CollapsePair.upper).toFinset

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.10 (core).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.core`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.core` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.core

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def core {K L : PreAbstractSimplicialComplex V} (S : Sequence K L)

    (H : Finset (Finset V)) : PreAbstractSimplicialComplex V :=

  L ⊔ simplices (skippedTops S.pairs H)

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.11 (future_upper_in_retained).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.future_upper_in_retained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.future_upper_in_retained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.future_upper_in_retained

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem future_upper_in_retained (P : CollapsePair V) {L}

    (T : Sequence P.retained L) {Q : CollapsePair V} (hQ : Q ∈ T.pairs)

    {s : Finset V} (hn : s.Nonempty) (hs : s ⊆ Q.upper) : s ∈ P.retained :=

by

  have bound : ∀ {A B : PreAbstractSimplicialComplex V} (U : Sequence A B)

      {R : CollapsePair V}, R ∈ U.pairs → R.ambient ≤ A := by

    intro A B U

    induction U with

    | refl => simp [Sequence.pairs]

    | step R U ih =>

      intro Q hQ

      change Q ∈ R :: U.pairs at hQ

      rcases List.mem_cons.mp hQ with rfl | hQ

      · exact le_rfl

      · exact (ih hQ).trans R.retained_le

  exact bound T hQ ((Q.ambient.isRelLowerSet_faces Q.upper_mem).2 hs hn)

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.12 (future_upper_cannot_resurrect).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.future_upper_cannot_resurrect`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.future_upper_cannot_resurrect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.future_upper_cannot_resurrect

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem future_upper_cannot_resurrect (P : CollapsePair V) {L}

    (T : Sequence P.retained L) {Q : CollapsePair V} (hQ : Q ∈ T.pairs) :

    ¬P.lower ⊆ Q.upper ∧ ¬P.upper ⊆ Q.upper := by

  have hl : ¬P.lower ⊆ Q.upper := by

    intro hs

    have hp := future_upper_in_retained P T hQ P.lower_nonempty hs

    exact hp.2 le_rfl

  exact ⟨hl,fun hu => hl ((Finset.subset_insert P.apex P.lower).trans hu)⟩

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.13 (core_le).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.core_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.core_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.core_le

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem core_le {K L} (S : Sequence K L) (H) : core S H ≤ K := by

  induction S generalizing H with

  | refl K => rw [core_refl]

  | step P T ih =>

    rw [core_step]

    split_ifs

    · exact sup_le ((ih _).trans P.retained_le) (upper_closure_le P)

    · exact (ih _).trans P.retained_le

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.14 (core_preserves).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.core_preserves`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.core_preserves` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.core_preserves

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem core_preserves {K L} (S : Sequence K L) (H) {s : Finset V}

    (hs : s ∈ K) (hprotect : ∃ q ∈ H, s ⊆ q) : s ∈ core S H := by

  revert hs hprotect

  induction S generalizing H with

  | refl K => intro hs _; simpa [core_refl] using hs

  | step P T ih =>

    intro hs hprotect

    rw [core_step]

    by_cases hb : blocked H P

    · rw [if_pos hb]

      by_cases hl : P.lower ⊆ s

      · right

        refine ⟨(P.ambient.isRelLowerSet_faces hs).1,P.upper,by simp,?_⟩

        rcases cofaces P hs hl with rfl | rfl

        · exact Finset.subset_insert P.apex P.lower

        · exact le_rfl

      · left

        exact ih (insert P.upper H) ⟨hs,hl⟩ (by

          obtain ⟨q,hq,hsq⟩ := hprotect; exact ⟨q,mem_insert_of_mem hq,hsq⟩)

    · rw [if_neg hb]

      apply ih H

      · refine ⟨hs,?_⟩

        intro hl

        obtain ⟨q,hq,hsq⟩ := hprotect

        exact hb ⟨q,hq,hl.trans hsq⟩

      · exact hprotect

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.15 (core_exact).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.core_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.core_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.core_exact

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem core_exact {K L} (S : Sequence K L) (H) (s : Finset V) :

    s ∈ core S H ↔ s ∈ L ∨ ∃ P ∈ skipped S.pairs H, s = P.lower ∨ s = P.upper := by

  induction S generalizing H with

  | refl K => simp [core_refl,skipped,Sequence.pairs]

  | step P T ih =>

    rw [core_step]

    by_cases hb : blocked H P

    · rw [if_pos hb]

      simp only [Sequence.pairs,skipped,if_pos hb,List.mem_cons]

      constructor

      · rintro (hs | hs)

        · rcases (ih _).mp hs with h | ⟨Q,hQ,he⟩

          · exact Or.inl h

          · exact Or.inr ⟨Q,Or.inr hQ,he⟩

        · have hK := upper_closure_le P hs

          by_cases hl : P.lower ⊆ s

          · exact Or.inr ⟨P,Or.inl rfl,cofaces P hK hl⟩

          · have ht := core_preserves T (insert P.upper H) ⟨hK,hl⟩ (by

              obtain ⟨hn,q,hq,hsq⟩ := hs

              have : q = P.upper := by simpa using hq

              subst q; exact ⟨P.upper,by simp,hsq⟩)

            rcases (ih _).mp ht with h | ⟨Q,hQ,he⟩

            · exact Or.inl h

            · exact Or.inr ⟨Q,Or.inr hQ,he⟩

      · rintro (hs | ⟨Q,hQ,he⟩)

        · exact Or.inl ((ih _).mpr (Or.inl hs))

        · rcases hQ with hQP | hQ

          · subst Q

            right

            rcases he with rfl | rfl

            · exact ⟨P.lower_nonempty,P.upper,by simp,Finset.subset_insert P.apex P.lower⟩

            · exact ⟨P.lower_nonempty.mono (Finset.subset_insert P.apex P.lower),P.upper,by simp,le_rfl⟩

          · exact Or.inl ((ih _).mpr (Or.inr ⟨Q,hQ,he⟩))

    · simpa only [if_neg hb,Sequence.pairs,skipped] using ih H

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.16 (core_faces_exact).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.core_faces_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.core_faces_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.core_faces_exact

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem core_faces_exact {K L} (S : Sequence K L) (H) :

    (core S H).faces = L.faces ∪

      {s | ∃ P ∈ skipped S.pairs H, s = P.lower ∨ s = P.upper} := by

  ext s

  exact core_exact S H s

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.17 (restrictPair).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.restrictPair`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.restrictPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.restrictPair

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def restrictPair (P : CollapsePair V) (A : PreAbstractSimplicialComplex V)

    (hA : A ≤ P.ambient) (hu : P.upper ∈ A) : CollapsePair V where

  ambient := A

  lower := P.lower

  apex := P.apex

  lower_nonempty := P.lower_nonempty

  apex_notMem := P.apex_notMem

  upper_mem := hu

  free s hs hls := P.free s (hA hs) hls

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.18 (unionPair).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.unionPair`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.unionPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.unionPair

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def unionPair (P : CollapsePair V) (H : Finset (Finset V))

    (h : ¬ blocked H P) : CollapsePair V where

  ambient := P.ambient ⊔ simplices H

  lower := P.lower

  apex := P.apex

  lower_nonempty := P.lower_nonempty

  apex_notMem := P.apex_notMem

  upper_mem := Or.inl P.upper_mem

  free := by

    intro s hs hls

    rcases hs with hs | ⟨hn,q,hq,hsq⟩

    · exact P.free s hs hls

    · exact False.elim (h ⟨q,hq,hls.1.trans hsq⟩)

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.19 (protectedReplay).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.protectedReplay`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.protectedReplay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.protectedReplay

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def protectedReplay {K L} (S : Sequence K L) (H : Finset (Finset V)) :

    Sequence (K ⊔ simplices H) (core S H ⊔ simplices H) := by

  classical

  induction S generalizing H with

  | refl K => exact (Sequence.refl _).cast rfl (by rw [core_refl])

  | step P T ih =>

    by_cases hb : blocked H P

    · exact (ih (insert P.upper H)).cast (by

        rw [show insert P.upper H = H ∪ {P.upper} by ext q; simp [or_comm],

          simplices_union]

        calc

          P.retained ⊔ (simplices H ⊔ simplices {P.upper}) =

              (P.retained ⊔ simplices {P.upper}) ⊔ simplices H := by ac_rfl

          _ = P.ambient ⊔ simplices H := by rw [restored]) (by

        rw [core_step,if_pos hb]

        rw [show insert P.upper H = H ∪ {P.upper} by ext q; simp [or_comm],

          simplices_union]

        ac_rfl)

    · exact (Sequence.step (unionPair P H hb)

        ((ih H).cast (unionPair_retained P H hb).symm rfl)).cast rfl (by

          rw [core_step,if_neg hb])

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.20 (protectedReplay_pairs).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.protectedReplay_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.protectedReplay_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.protectedReplay_pairs

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem protectedReplay_pairs {K L} (S : Sequence K L) (H) :

    (protectedReplay S H).pairs.map (fun P => (P.lower,P.upper)) =

      (emitted S.pairs H).map (fun P => (P.lower,P.upper)) := by

  induction S generalizing H with

  | refl K => simp [protectedReplay,emitted,Sequence.pairs,Sequence.pairs_cast]

  | step P T ih =>

    by_cases hb : blocked H P

    · simp only [protectedReplay,dif_pos hb,Sequence.pairs_cast,Sequence.pairs,emitted,if_pos hb]

      exact ih (insert P.upper H)

    · simp only [protectedReplay,dif_neg hb,Sequence.pairs_cast,Sequence.pairs,emitted,if_neg hb,List.map_cons]

      exact congrArg (List.cons (P.lower,P.upper)) (ih H)

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.21 (standaloneReplay).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.standaloneReplay`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.standaloneReplay` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.standaloneReplay

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def standaloneReplay {K L} (S : Sequence K L) (H : Finset (Finset V)) :

    Sequence (core S H) L := by

  classical

  induction S generalizing H with

  | refl K => exact (Sequence.refl K).cast (core_refl K H).symm rfl

  | step P T ih =>

    by_cases hb : blocked H P

    · let Q := restrictPair P (core (.step P T) H) (core_le _ _) (by

        rw [core_step,if_pos hb]; right

        exact ⟨P.lower_nonempty.mono (Finset.subset_insert P.apex P.lower),P.upper,by simp,le_rfl⟩)

      exact Sequence.step Q ((ih (insert P.upper H)).cast

        (restricted_retained P T H hb).symm rfl)

    · exact (ih H).cast (by rw [core_step,if_neg hb]) rfl

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.22 (standaloneReplay_pairs).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.standaloneReplay_pairs`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.standaloneReplay_pairs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.standaloneReplay_pairs

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem standaloneReplay_pairs {K L} (S : Sequence K L) (H) :

    (standaloneReplay S H).pairs.map (fun P => (P.lower,P.upper)) =

      (skipped S.pairs H).map (fun P => (P.lower,P.upper)) := by

  induction S generalizing H with

  | refl K => simp [standaloneReplay,skipped,Sequence.pairs,Sequence.pairs_cast]

  | step P T ih =>

    by_cases hb : blocked H P

    · simp only [standaloneReplay,dif_pos hb,Sequence.pairs_cast,Sequence.pairs,skipped,if_pos hb,List.map_cons]

      exact congrArg (List.cons (P.lower,P.upper)) (ih (insert P.upper H))

    · simp only [standaloneReplay,dif_neg hb,Sequence.pairs_cast,Sequence.pairs,skipped,if_neg hb]

      exact ih H

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.23 (standaloneWithTail).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.standaloneWithTail`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.standaloneWithTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.standaloneWithTail

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def standaloneWithTail {K L M} (S : Sequence K L) (H)

    (tail : Sequence L M) : Sequence (core S H) M :=

  (standaloneReplay S H).append tail

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.24 (emitted_nonempty).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.emitted_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.emitted_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.emitted_nonempty

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem emitted_nonempty {K L} (S : Sequence K L) (H) :

    ∀ P ∈ emitted S.pairs H, P.lower.Nonempty := by

  intro P _; exact P.lower_nonempty

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.25 (outside_coface_criterion).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.outside_coface_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.outside_coface_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.outside_coface_criterion

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem outside_coface_criterion (P : CollapsePair V) (H)

    (hout : ∀ q ∈ H, q ∉ P.ambient) :

    (∀ s ∈ P.ambient ⊔ simplices H, P.lower ⊆ s →

      s = P.lower ∨ s = P.upper) ↔ ¬blocked H P := by

  constructor

  · intro hf hb

    obtain ⟨q,hq,hlq⟩ := hb

    have hn := P.lower_nonempty.mono hlq

    rcases hf q (Or.inr ⟨hn,q,hq,le_rfl⟩) hlq with he | he

    · exact hout q hq (he.symm ▸ P.lower_mem)

    · exact hout q hq (he.symm ▸ P.upper_mem)

  · intro h s hs hl

    rcases hs with hs | ⟨hn,q,hq,hsq⟩

    · exact cofaces P hs hl

    · exact False.elim (h ⟨q,hq,hl.trans hsq⟩)

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.26 (critical_boundary).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.critical_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.critical_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.critical_boundary

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem critical_boundary {K L} (S : Sequence K L) (H)

    (hout : ∀ q ∈ H, q ∉ K)

    (hbd : ∀ q ∈ H, ∀ s, s.Nonempty → s ⊂ q → s ∈ K) :

    (∀ q ∈ H, q ∉ core S H) ∧

      (∀ q ∈ H, ∀ s, s.Nonempty → s ⊂ q → s ∈ core S H) := by

  constructor

  · intro q hq hc; exact hout q hq (core_le S H hc)

  · intro q hq s hn hs

    exact core_preserves S H (hbd q hq s hn hs) ⟨q,hq,hs.1⟩

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.27 (critical_antichain).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.critical_antichain`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.critical_antichain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.critical_antichain

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem critical_antichain (K : PreAbstractSimplicialComplex V) (H : Finset (Finset V))

    (hne : ∀ q ∈ H, q.Nonempty) (hout : ∀ q ∈ H, q ∉ K)

    (hbd : ∀ q ∈ H, ∀ s, s.Nonempty → s ⊂ q → s ∈ K) :

    ∀ q ∈ H, ∀ r ∈ H, q ⊆ r → q = r := by

  intro q hq r hr hqr

  by_contra he

  exact hout q hq (hbd r hr q (hne q hq)

    (Finset.ssubset_iff_subset_ne.mpr ⟨hqr,he⟩))

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.28 (scan_append).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.scan_append`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.scan_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.scan_append

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem scan_append (xs ys : List (CollapsePair V)) (H) :

    skipped (xs ++ ys) H = skipped xs H ++ skipped ys (advance xs H) ∧

    emitted (xs ++ ys) H = emitted xs H ++ emitted ys (advance xs H) := by

  induction xs generalizing H with

  | nil => simp [skipped,emitted,advance]

  | cons P xs ih =>

    by_cases hb : blocked H P <;>

      simp [skipped,emitted,advance,hb,ih,List.cons_append]

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.29 (advance_exact).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.advance_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.advance_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.advance_exact

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem advance_exact (xs : List (CollapsePair V)) (H) :

    advance xs H = H ∪ skippedTops xs H := by

  induction xs generalizing H with

  | nil => simp [advance,skippedTops,skipped]

  | cons P xs ih =>

    by_cases hb : blocked H P <;>

      simp [advance,skippedTops,skipped,hb,ih,Finset.insert_union,

        Finset.union_insert,Finset.union_assoc,Finset.union_left_comm,Finset.union_comm]

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.30 (prefix_invariant).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.prefix_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.prefix_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.prefix_invariant

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem prefix_invariant {K B L : PreAbstractSimplicialComplex V}

    (A : Sequence K B) (T : Sequence B L) (H) :

    core A H ⊔ simplices H = B ⊔ simplices (skippedTops A.pairs H) ⊔ simplices H ∧

    B ⊔ simplices (advance A.pairs H) = core A H ⊔ simplices H := by

  constructor

  · rfl

  · rw [advance_exact,simplices_union]

    unfold core

    ac_rfl

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.31 (native_current_cofaces).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.native_current_cofaces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.native_current_cofaces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.native_current_cofaces

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem native_current_cofaces (P : CollapsePair V) (s : Finset V) :

    (s ∈ P.ambient ∧ P.lower ⊆ s) ↔ s = P.lower ∨ s = P.upper := by

  constructor

  · rintro ⟨hs,hl⟩; exact cofaces P hs hl

  · rintro (rfl | rfl)

    · exact ⟨P.lower_mem,le_rfl⟩

    · exact ⟨P.upper_mem,Finset.subset_insert P.apex P.lower⟩

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.32 (decision_at_prefix).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.decision_at_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.decision_at_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.decision_at_prefix

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem decision_at_prefix (xs : List (CollapsePair V)) (H) (P : CollapsePair V) :

    blocked (advance xs H) P ↔

      (∃ q ∈ H, P.lower ⊆ q) ∨

        ∃ Q ∈ skipped xs H, P.lower ⊆ Q.upper := by

  rw [advance_exact]

  simp only [blocked,Finset.mem_union,skippedTops,List.mem_toFinset,List.mem_map]

  constructor

  · rintro ⟨q,hq,hl⟩

    rcases hq with hq | ⟨Q,hQ,rfl⟩

    · exact Or.inl ⟨q,hq,hl⟩

    · exact Or.inr ⟨Q,hQ,hl⟩

  · rintro (⟨q,hq,hl⟩ | ⟨Q,hQ,hl⟩)

    · exact ⟨q,Or.inl hq,hl⟩

    · exact ⟨Q.upper,Or.inr ⟨Q,hQ,rfl⟩,hl⟩

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.33 (skippedIndexed).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.skippedIndexed`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.skippedIndexed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.skippedIndexed

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def skippedIndexed : List (CollapsePair V) → Finset (Finset V) → Nat →

    List (Nat × CollapsePair V)

  | [], _, _ => []

  | P :: ps, H, n => if blocked H P then

      (n,P) :: skippedIndexed ps (insert P.upper H) (n+1)

    else skippedIndexed ps H (n+1)

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.34 (emittedIndexed).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.emittedIndexed`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.emittedIndexed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.emittedIndexed

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def emittedIndexed : List (CollapsePair V) → Finset (Finset V) → Nat →

    List (Nat × CollapsePair V)

  | [], _, _ => []

  | P :: ps, H, n => if blocked H P then

      emittedIndexed ps (insert P.upper H) (n+1)

    else (n,P) :: emittedIndexed ps H (n+1)

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.35 (skippedIndices).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.skippedIndices`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.skippedIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.skippedIndices

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def skippedIndices (ps : List (CollapsePair V)) (H : Finset (Finset V)) : List Nat :=

  (skippedIndexed ps H 0).map Prod.fst

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Definition 1.36 (emittedIndices).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.emittedIndices`

*Formalization.* `D5/S3/Geometry/FinitePrescribedPairProtection.emittedIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.emittedIndices

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

def emittedIndices (ps : List (CollapsePair V)) (H : Finset (Finset V)) : List Nat :=

  (emittedIndexed ps H 0).map Prod.fst

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.37 (indexed_scan).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.indexed_scan`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.indexed_scan` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.indexed_scan

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem indexed_scan (ps : List (CollapsePair V)) (H) (n : Nat) :

    (skippedIndexed ps H n).map Prod.snd = skipped ps H ∧

    (emittedIndexed ps H n).map Prod.snd = emitted ps H := by

  induction ps generalizing H n with

  | nil => simp [skippedIndexed,emittedIndexed,skipped,emitted]

  | cons P ps ih =>

    by_cases hb : blocked H P <;>

      simp [skippedIndexed,emittedIndexed,skipped,emitted,hb,ih]

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.38 (indexed_bounds).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.indexed_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.indexed_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.indexed_bounds

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem indexed_bounds (ps : List (CollapsePair V)) (H) (n : Nat) :

    (∀ z ∈ skippedIndexed ps H n, n ≤ z.1 ∧ z.1 < n + ps.length) ∧

    (∀ z ∈ emittedIndexed ps H n, n ≤ z.1 ∧ z.1 < n + ps.length) := by

  induction ps generalizing H n with

  | nil => simp [skippedIndexed,emittedIndexed]

  | cons P ps ih =>

    by_cases hb : blocked H P

    · simp only [skippedIndexed,emittedIndexed,if_pos hb,List.length_cons,List.mem_cons]

      constructor

      · intro z hz

        rcases hz with rfl | hz

        · simp

        · have hh := (ih (insert P.upper H) (n+1)).1 z hz

          constructor <;> omega

      · intro z hz

        have hh := (ih (insert P.upper H) (n+1)).2 z hz

        constructor <;> omega

    · simp only [skippedIndexed,emittedIndexed,if_neg hb,List.length_cons,List.mem_cons]

      constructor

      · intro z hz

        have hh := (ih H (n+1)).1 z hz

        constructor <;> omega

      · intro z hz

        rcases hz with rfl | hz

        · simp

        · have hh := (ih H (n+1)).2 z hz

          constructor <;> omega

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.39 (empty_protection).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.empty_protection`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.empty_protection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.empty_protection

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

theorem empty_protection (ps : List (CollapsePair V)) :

    skipped ps ∅ = [] ∧ emitted ps ∅ = ps := by

  induction ps with

  | nil => simp [skipped,emitted]

  | cons P ps ih => simp [skipped,emitted,blocked,ih]

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

**Theorem 1.40 (core_empty).**

Lean statement: `D5/S3/Geometry/FinitePrescribedPairProtection.core_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FinitePrescribedPairProtection.core_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

D5.S3.Geometry.FinitePrescribedPairProtection.core_empty

SOURCE scope (literal source context, not an elaborated telescope):

noncomputable section; open Finset; namespace D5.S3.Geometry.FinitePrescribedPairProtection; open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse; variable {V : Type*} [Fintype V] [DecidableEq V].

Exact public SOURCE declaration and proof/body:

@[simp] theorem core_empty {K L} (S : Sequence K L) : core S ∅ = L := by

  simp [core,skippedTops,(empty_protection S.pairs).1]

FromLean resolves the source-qualified declaration; no catalog, emit, kernel, Reg or admission success is claimed.

## References

- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.advance`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.advance_exact`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.blocked`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.core`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.core_empty`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.core_exact`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.core_faces_exact`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.core_le`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.core_preserves`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.critical_antichain`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.critical_boundary`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.decision_at_prefix`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.emitted`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.emittedIndexed`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.emittedIndices`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.emitted_nonempty`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.empty_protection`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.future_upper_cannot_resurrect`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.future_upper_in_retained`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.indexed_bounds`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.indexed_scan`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.mem_simplices`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.native_current_cofaces`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.outside_coface_criterion`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.prefix_invariant`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.protectedReplay`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.protectedReplay_pairs`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.restrictPair`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.scan_append`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.simplices`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.simplices_empty`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.simplices_union`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.skipped`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.skippedIndexed`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.skippedIndices`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.skippedTops`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.standaloneReplay`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.standaloneReplay_pairs`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.standaloneWithTail`
- Truth anchor: `D5/S3/Geometry/FinitePrescribedPairProtection.unionPair`
- Dependency: [D5/S3/Geometry/FiniteRelativeSimplicialCollapse](FiniteRelativeSimplicialCollapse.md)
