/- GID: D5/S3/Quantum/Recovery/OrthogonalSyndromeDecoding
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/OrthogonalSyndromeDecoding
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Orthogonal syndrome decoding preserves every logical matrix. -/

import Mathlib

/-!
# Orthogonal syndrome decoding

The encoding and support-restricted decoder are explicit finite matrix sums.
Their algebraic identity permits arbitrary syndrome coherence. Positivity and
the completely-positive completion outside the represented support are separate
statements. The classical recovery mechanism is attributed to Knill and Laflamme,
Phys. Rev. A 55 (1997) 900, doi:10.1103/PhysRevA.55.900.
-/

noncomputable section
open scoped Matrix BigOperators

namespace D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {s n d : Type*} [Fintype s] [DecidableEq s]
  [Fintype n] [Fintype d] [DecidableEq d]

/-- An orthogonal family of full logical copies. -/
def OrthogonalSyndromes (S : s → Matrix n d ℂ) : Prop :=
  ∀ i j, (S i)ᴴ * S j = if i = j then 1 else 0

/-- Append a syndrome matrix using a concrete orthogonal-copy embedding. -/
def syndromeEncoding (S : s → Matrix n d ℂ)
    (sigma : Matrix s s ℂ) (rho : Matrix d d ℂ) : Matrix n n ℂ :=
  ∑ j, ∑ k, sigma j k • (S j * rho * (S k)ᴴ)

/-- Decode and forget the orthogonal syndrome, on the represented support. -/
def syndromeDecoding (S : s → Matrix n d ℂ)
    (state : Matrix n n ℂ) : Matrix d d ℂ :=
  ∑ i, (S i)ᴴ * state * S i

private theorem decoding_sum {t : Type*} [Fintype t]
    (S : s → Matrix n d ℂ) (state : t → Matrix n n ℂ) :
    syndromeDecoding S (∑ a, state a) =
      ∑ a, syndromeDecoding S (state a) := by
  simp only [syndromeDecoding, Matrix.mul_sum, Matrix.sum_mul]
  rw [Finset.sum_comm]

private theorem decoding_smul (S : s → Matrix n d ℂ)
    (c : ℂ) (state : Matrix n n ℂ) :
    syndromeDecoding S (c • state) = c • syndromeDecoding S state := by
  simp only [syndromeDecoding, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]

/-- Off-diagonal syndrome blocks disappear, while diagonal blocks preserve
exactly the original logical matrix. -/
theorem decoding_syndrome_block (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (rho : Matrix d d ℂ) (j k : s) :
    syndromeDecoding S (S j * rho * (S k)ᴴ) =
      if j = k then rho else 0 := by
  have term (i : s) :
      (S i)ᴴ * (S j * rho * (S k)ᴴ) * S i =
        if i = j then (if k = i then rho else 0) else 0 := by
    calc
      (S i)ᴴ * (S j * rho * (S k)ᴴ) * S i =
          ((S i)ᴴ * S j) * rho * ((S k)ᴴ * S i) := by
        simp only [Matrix.mul_assoc]
      _ = if i = j then (if k = i then rho else 0) else 0 := by
        rw [hS i j, hS k i]
        split_ifs <;> simp
  simp only [syndromeDecoding, term]
  simp [eq_comm]

/-- Exact matrix recovery, including arbitrary syndrome coherence.
The normalization scalar is computed from the actual syndrome trace. -/
theorem orthogonal_syndrome_recovery (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S)
    (sigma : Matrix s s ℂ) (rho : Matrix d d ℂ) :
    syndromeDecoding S (syndromeEncoding S sigma rho) =
      Matrix.trace sigma • rho := by
  unfold syndromeEncoding
  simp_rw [decoding_sum, decoding_smul,
    decoding_syndrome_block S hS rho]
  simp [smul_ite, Matrix.trace, Matrix.diag_apply, Finset.sum_smul]

/-- A trace-one syndrome is exactly irrelevant to the recovered logical state. -/
theorem trace_one_syndrome_recovery (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S)
    (sigma : Matrix s s ℂ) (hTrace : Matrix.trace sigma = 1)
    (rho : Matrix d d ℂ) :
    syndromeDecoding S (syndromeEncoding S sigma rho) = rho := by
  rw [orthogonal_syndrome_recovery S hS, hTrace, one_smul]

/-- Logical unitary transport within each syndrome preserves orthogonality.
This constructs the corrected decoding frame for a known syndrome history. -/
theorem syndrome_transport_orthogonal (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (V : s → Matrix d d ℂ)
    (hV : ∀ i, (V i)ᴴ * V i = 1) :
    OrthogonalSyndromes (fun i => S i * V i) := by
  intro i j
  calc
    (S i * V i)ᴴ * (S j * V j) =
        (V i)ᴴ * ((S i)ᴴ * S j) * V j := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = if i = j then 1 else 0 := by
      rw [hS i j]
      by_cases hij : i = j
      · subst j
        simpa using hV i
      · simp [hij]

/-- A decoder that transports every syndrome frame recovers all logical
matrices even when different syndromes carry different logical holonomies. -/
theorem transported_syndrome_recovery (S : s → Matrix n d ℂ)
    (hS : OrthogonalSyndromes S) (V : s → Matrix d d ℂ)
    (hV : ∀ i, (V i)ᴴ * V i = 1)
    (sigma : Matrix s s ℂ) (hTrace : Matrix.trace sigma = 1)
    (rho : Matrix d d ℂ) :
    syndromeDecoding (fun i => S i * V i)
      (syndromeEncoding (fun i => S i * V i) sigma rho) = rho := by
  exact trace_one_syndrome_recovery _
    (syndrome_transport_orthogonal S hS V hV) sigma hTrace rho

#print axioms decoding_syndrome_block
#print axioms orthogonal_syndrome_recovery
#print axioms trace_one_syndrome_recovery
#print axioms syndrome_transport_orthogonal
#print axioms transported_syndrome_recovery

end D5.S3.Quantum.Recovery.OrthogonalSyndromeDecoding
