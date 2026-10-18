/- GID: D5/S3/FiniteGroups/FiniteOttoCongruence
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/FiniteOttoCongruence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Finite semigroups with an Otto congruence have cancellative quotients. -/

/- proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#17635; Proved)
   Direct frozen dependencies: result and the power-dependent helpers use
   D5/S0/Certificates/Algebra/BergmanQuestion15Refutation.positivePower,
   declaration statement_id:
   sha256:abf65a40df0887f1b9284248d92e03010aa0b9ac5129849f1092ed7f22e58716.
   Otto, OttoIsCongruence, QuotientCancelative and claim follow the expressions
   in #17635. The existing positivePower is used without a forwarding alias.
   proof_shape: otto_refl: bind-only; consumers: idempotent_class_identity,
     otto_left_cancel; Direct frozen dependencies: none; escape_witness: none.
   proof_shape: otto_symm: bind-only; consumers: idempotent_class_identity,
     otto_left_cancel; Direct frozen dependencies: none; escape_witness: none.
   proof_shape: otto_trans: bind-only; consumers: idempotent_class_identity,
     otto_left_cancel, quotient_cancelative;
     Direct frozen dependencies: none; escape_witness: none.
   proof_shape: p_mul: bind-only; consumers: p_comm, exists_idempotent_power,
     inverse_class; Direct frozen dependencies: positivePower above; escape_witness: none.
   proof_shape: p_comm: bind-only; consumers: otto_stable_power,
     idempotent_class_identity;
     Direct frozen dependencies: positivePower above; escape_witness: none.
   proof_shape: exists_idempotent_power: bind-only; consumers: inverse_class,
     idempotent_class_identity, otto_left_cancel;
     Direct frozen dependencies: positivePower above; escape_witness: none.
   proof_shape: otto_idempotents: bind-only; consumers: idempotent_class_identity,
     inverse_class; Direct frozen dependencies: none; escape_witness: none.
   proof_shape: otto_stable_power: bind-only; consumer: idempotent_class_identity;
     Direct frozen dependencies: positivePower above; escape_witness: none.
   proof_shape: otto_mul_swap: bind-only; consumer: quotient_cancelative;
     Direct frozen dependencies: none; escape_witness: none.
   proof_shape: idempotent_class_identity: bind-only; consumer: otto_left_cancel;
     Direct frozen dependencies: positivePower above; escape_witness: none.
   proof_shape: inverse_class: bind-only; consumer: otto_left_cancel;
     Direct frozen dependencies: positivePower above; escape_witness: none.
   proof_shape: otto_left_cancel: bind-only; consumer: quotient_cancelative;
     Direct frozen dependencies: positivePower above; escape_witness: none.
   proof_shape: quotient_cancelative: bind-only; consumer: result;
     Direct frozen dependencies: positivePower above; escape_witness: none.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17715.
   utility none: structural theorems for arbitrary finite semigroups, with no
   enumeration, numerical reduction, checker or certified concrete instance. -/
import Mathlib.Topology.Algebra.Semigroup
import D5.S0.Certificates.Algebra.BergmanQuestion15Refutation

namespace D5.S3.FiniteGroups.FiniteOttoCongruence

/-- Otto conjugacy (arXiv:2411.16284, Section 2): `a ∼o b` iff `a g = g b` and `b h = h a` for some `g h ∈ S`. -/
def Otto {S : Type*} [Semigroup S] (a b : S) : Prop :=
  ∃ g h : S, a * g = g * b ∧ b * h = h * a

/-- `∼o` is a congruence: compatible with multiplication on both sides (it is always an equivalence relation). -/
def OttoIsCongruence (S : Type*) [Semigroup S] : Prop :=
  ∀ a b c d : S, Otto a b → Otto c d → Otto (a * c) (b * d)

/-- `S/∼o` is cancelative, in terms of classes: `[a][b] = [a][c] → [b] = [c]` and `[b][a] = [c][a] → [b] = [c]`. -/
def QuotientCancelative (S : Type*) [Semigroup S] : Prop :=
  (∀ a b c : S, Otto (a * b) (a * c) → Otto b c) ∧ ∀ a b c : S, Otto (b * a) (c * a) → Otto b c

/-- Problem 9.4 asks whether some finite semigroup has `∼o` a congruence and `S/∼o` not cancelative; the claim is the
negative answer: for every finite semigroup with `∼o` a congruence, `S/∼o` is cancelative. -/
def claim : Prop :=
  ∀ (S : Type) [Semigroup S] [Finite S], OttoIsCongruence S → QuotientCancelative S


open D5.S0.Certificates.Algebra.BergmanQuestion15Refutation (positivePower)

variable {S : Type*} [Semigroup S]

private theorem otto_refl (a : S) : Otto a a := by
  exact ⟨a, a, rfl, rfl⟩

private theorem otto_symm {a b : S} (h : Otto a b) : Otto b a := by
  obtain ⟨g, k, hg, hk⟩ := h
  exact ⟨k, g, hk, hg⟩

private theorem otto_trans {a b c : S} (hab : Otto a b) (hbc : Otto b c) : Otto a c := by
  obtain ⟨g, h, hg, hh⟩ := hab
  obtain ⟨u, v, hu, hv⟩ := hbc
  exact ⟨g * u, v * h, (SemiconjBy.mul_left hg.symm hu.symm).symm,
    (SemiconjBy.mul_left hv.symm hh.symm).symm⟩

private theorem p_mul (a : S) (i j : ℕ) : positivePower a i * positivePower a j = positivePower a (i + j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change positivePower a i * (positivePower a j * a) = positivePower a (i + (j + 1) + 1)
    rw [← mul_assoc, ih]
    rfl

private theorem p_comm (a : S) (i j : ℕ) : positivePower a i * positivePower a j = positivePower a j * positivePower a i := by
  simp only [p_mul, Nat.add_comm i j]

private theorem exists_idempotent_power [Finite S] (a : S) :
    ∃ k : ℕ, 2 ≤ k ∧ IsIdempotentElem (positivePower a k) := by
  let : TopologicalSpace S := ⊥
  let : DiscreteTopology S := ⟨rfl⟩
  let T : Set S := {x | ∃ k : ℕ, 2 ≤ k ∧ positivePower a k = x}
  obtain ⟨e, ⟨k, hk, he⟩, hid⟩ :=
    exists_idempotent_in_compact_subsemigroup
      (fun _ => continuous_of_discreteTopology) T
      ⟨positivePower a 2, 2, le_rfl, rfl⟩ (Set.toFinite T).isCompact (by
        rintro x ⟨i, hi, rfl⟩ y ⟨j, hj, rfl⟩
        exact ⟨i + j + 1, by omega, (p_mul a i j).symm⟩)
  exact ⟨k, hk, by simpa only [IsIdempotentElem, he] using hid⟩

private theorem otto_idempotents {e f : S} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : Otto e f := by
  refine ⟨e * f, f * e, ?_, ?_⟩
  · rw [← mul_assoc, he.eq, mul_assoc, hf.eq]
  · rw [← mul_assoc, hf.eq, mul_assoc, he.eq]

private theorem otto_stable_power (a : S) (k : ℕ) (he : IsIdempotentElem (positivePower a k)) :
    Otto a (positivePower a (k+1)) := by
  have hc : a * positivePower a k = positivePower a k * a := p_comm a 0 k
  change a * positivePower a k = positivePower a k * a at hc
  have hl : positivePower a k * positivePower a (k+1) = positivePower a k * a := by
    change positivePower a k * (positivePower a k * a) = positivePower a k * a
    exact he.mul_self_mul a
  have hr : positivePower a (k+1) * positivePower a k = positivePower a k * a := by
    rw [p_comm a (k+1) k, hl]
  exact ⟨positivePower a k, positivePower a k, hc.trans hl.symm, hr⟩

private theorem otto_mul_swap (a b : S) : Otto (a*b) (b*a) := by
  exact ⟨a, b, mul_assoc a b a, mul_assoc b a b⟩


private theorem idempotent_class_identity [Finite S] (h : OttoIsCongruence S)
    (e : S) (he : IsIdempotentElem e) (a : S) :
    Otto (e*a) a ∧ Otto (a*e) a := by
  obtain ⟨k, hk, hpk⟩ := exists_idempotent_power a
  have heq := otto_idempotents he hpk
  have ha := otto_stable_power a k hpk
  have hleft := h e (positivePower a k) a a heq (otto_refl a)
  have hright := h a a e (positivePower a k) (otto_refl a) heq
  have hp : positivePower a k * a = positivePower a (k+1) := rfl
  have hp' : a * positivePower a k = positivePower a (k+1) := by
    exact (p_comm a 0 k).trans hp
  exact ⟨otto_trans (by simpa only [hp] using hleft) (otto_symm ha),
    otto_trans (by simpa only [hp'] using hright) (otto_symm ha)⟩

private theorem inverse_class [Finite S] (e : S) (he : IsIdempotentElem e) (a : S) :
    ∃ b : S, Otto (a*b) e ∧ Otto (b*a) e := by
  obtain ⟨k, hk, hpk⟩ := exists_idempotent_power a
  refine ⟨positivePower a (k-1), ?_, ?_⟩
  · have hp : a * positivePower a (k-1) = positivePower a k := by
      change positivePower a 0 * positivePower a (k-1) = positivePower a k
      rw [p_mul]
      congr 1
      omega
    rw [hp]
    exact otto_idempotents hpk he
  · have hp : positivePower a (k-1) * a = positivePower a k := by
      change positivePower a (k-1) * positivePower a 0 = positivePower a k
      rw [p_mul]
      congr 1
      omega
    rw [hp]
    exact otto_idempotents hpk he

private theorem otto_left_cancel [Finite S] (h : OttoIsCongruence S)
    (a b c : S) (habc : Otto (a*b) (a*c)) : Otto b c := by
  obtain ⟨k, _, he⟩ := exists_idempotent_power a
  let e := positivePower a k
  obtain ⟨x, hax, hxa⟩ := inverse_class e he a
  have hb := otto_trans (h (x*a) e b b hxa (otto_refl b))
    (idempotent_class_identity h e he b).1
  have hc := otto_trans (h (x*a) e c c hxa (otto_refl c))
    (idempotent_class_identity h e he c).1
  have hmiddle := h x x (a*b) (a*c) (otto_refl x) habc
  rw [← mul_assoc, ← mul_assoc] at hmiddle
  exact otto_trans (otto_symm hb) (otto_trans hmiddle hc)

private theorem quotient_cancelative [Finite S] (h : OttoIsCongruence S) :
    QuotientCancelative S := by
  refine ⟨otto_left_cancel h, ?_⟩
  intro a b c habc
  exact otto_left_cancel h a b c
    (otto_trans (otto_mul_swap a b) (otto_trans habc (otto_mul_swap c a)))

theorem result : claim := by
  intro S _ _ h
  exact quotient_cancelative h


end D5.S3.FiniteGroups.FiniteOttoCongruence
