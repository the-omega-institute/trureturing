# FiniteGreedyFamilyTransport

## Abstract

Exact coordinate rounds commute with injective toggle maps, including original-label complementation.

Exact equality of remaining families under coordinate toggles, label maps and original-ground complements. Augmented empty faces are retained. Lexical section variables are recorded faithfully. Lean may omit unused variables.

**Definition 1.1 (flip).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.flip`

*Formalization.* `D5/S3/Geometry/FiniteGreedyFamilyTransport.flip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.flip.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

def flip (v : V) (a : Finset V) : Finset V

**Theorem 1.2 (mem_flip).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.mem_flip`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.mem_flip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.mem_flip.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

@[simp] theorem mem_flip (v x : V) (a : Finset V) :

    x ∈ flip v a ↔ (x = v ∧ v ∉ a) ∨ (x ≠ v ∧ x ∈ a)

**Theorem 1.3 (flip_flip).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.flip_flip`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.flip_flip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.flip_flip.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

@[simp] theorem flip_flip (v : V) (a : Finset V) : flip v (flip v a) = a

**Theorem 1.4 (mem_remaining).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.mem_remaining`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.mem_remaining` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.mem_remaining.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

@[simp] theorem mem_remaining (F : Finset (Finset V)) (v : V) (a : Finset V) :

    a ∈ remaining F v ↔ a ∈ F ∧ flip v a ∉ F

**Theorem 1.5 (remaining_image).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_image`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.remaining_image.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem remaining_image (F : Finset (Finset V)) (u : V) (v : W)

    (f : Finset V → Finset W) (hf : Function.Injective f)

    (hc : ∀ a, flip v (f a) = f (flip u a)) :

    remaining (F.image f) v = (remaining F u).image f

**Theorem 1.6 (survivors_image).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_image`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.survivors_image.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem survivors_image (F : Finset (Finset V)) (vs : List V)

    (f : Finset V → Finset W) (g : V → W) (hf : Function.Injective f)

    (hc : ∀ v ∈ vs, ∀ a, flip (g v) (f a) = f (flip v a)) :

    survivors (F.image f) (vs.map g) = (survivors F vs).image f

**Theorem 1.7 (survivors_map).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_map`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.survivors_map.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem survivors_map (e : V ↪ W) (F : Finset (Finset V)) (vs : List V) :

    survivors (F.image (Finset.map e)) (vs.map e) =

      (survivors F vs).image (Finset.map e)

**Definition 1.8 (complementMap).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.complementMap`

*Formalization.* `D5/S3/Geometry/FiniteGreedyFamilyTransport.complementMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.complementMap.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

def complementMap (e : V ↪ W) (a : Finset V) : Finset W

**Theorem 1.9 (remaining_complement).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.remaining_complement.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem remaining_complement (e : V ↪ W) (F : Finset (Finset V)) (v : V) :

    remaining (F.image (complementMap e)) (e v) =

      (remaining F v).image (complementMap e)

**Theorem 1.10 (survivors_complement).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.survivors_complement.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem survivors_complement (e : V ↪ W) (F : Finset (Finset V)) (vs : List V) :

    survivors (F.image (complementMap e)) (vs.map e) =

      (survivors F vs).image (complementMap e)

**Theorem 1.11 (remaining_union).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.remaining_union.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem remaining_union (A B : Finset (Finset V)) (v : V)

    (hab : ∀ a ∈ A, flip v a ∉ B) (hba : ∀ b ∈ B, flip v b ∉ A) :

    remaining (A ∪ B) v = remaining A v ∪ remaining B v

**Theorem 1.12 (survivors_union).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_union`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.survivors_union.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem survivors_union (A B : Finset (Finset V)) (vs : List V)

    (hab : ∀ v ∈ vs, ∀ a ∈ A, flip v a ∉ B)

    (hba : ∀ v ∈ vs, ∀ b ∈ B, flip v b ∉ A) :

    survivors (A ∪ B) vs = survivors A vs ∪ survivors B vs

**Theorem 1.13 (survivors_by_pin).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_by_pin`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_by_pin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.survivors_by_pin.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem survivors_by_pin (A B : Finset (Finset V)) (vs : List V) (p : V)

    (ha : ∀ a ∈ A, p ∉ a) (hb : ∀ b ∈ B, p ∈ b) (hp : p ∉ vs) :

    survivors (A ∪ B) vs = survivors A vs ∪ survivors B vs

**Theorem 1.14 (remaining_of_fixed).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_of_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_of_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.remaining_of_fixed.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem remaining_of_fixed (F : Finset (Finset V)) (v : V)

    (h : (∀ a ∈ F, v ∈ a) ∨ (∀ a ∈ F, v ∉ a)) : remaining F v = F

**Theorem 1.15 (remaining_insert).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.remaining_insert.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem remaining_insert (F : Finset (Finset V)) (v w : V) (hvw : v ≠ w)

    (hw : ∀ a ∈ F, w ∉ a) :

    remaining (F.image (insert w)) v = (remaining F v).image (insert w)

**Theorem 1.16 (survivors_insert).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_insert`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_insert` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.survivors_insert.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem survivors_insert (F : Finset (Finset V)) (vs : List V) (w : V)

    (hw : ∀ a ∈ F, w ∉ a) (hvs : w ∉ vs) :

    survivors (F.image (insert w)) vs = (survivors F vs).image (insert w)

**Definition 1.17 (computeSurvivors).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.computeSurvivors`

*Formalization.* `D5/S3/Geometry/FiniteGreedyFamilyTransport.computeSurvivors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.computeSurvivors.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

def computeSurvivors (F : Finset (Finset V)) : List V → Finset (Finset V)

**Theorem 1.18 (computeSurvivors_eq).**

Lean statement: `D5/S3/Geometry/FiniteGreedyFamilyTransport.computeSurvivors_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGreedyFamilyTransport.computeSurvivors_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteGreedyFamilyTransport.computeSurvivors_eq.

### Source text

Lexical source context (not a compiled telescope):

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

Definitions and proofs are in the paired Lean module.

theorem computeSurvivors_eq (F : Finset (Finset V)) (vs : List V) :

    computeSurvivors F vs = survivors F vs

## References

- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.complementMap`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.computeSurvivors`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.computeSurvivors_eq`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.flip`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.flip_flip`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.mem_flip`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.mem_remaining`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_complement`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_image`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_insert`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_of_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.remaining_union`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_by_pin`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_complement`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_image`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_insert`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_map`
- Truth anchor: `D5/S3/Geometry/FiniteGreedyFamilyTransport.survivors_union`
- Dependency: [D5/S3/Geometry/FiniteCoordinateGreedyMatching](FiniteCoordinateGreedyMatching.md)
