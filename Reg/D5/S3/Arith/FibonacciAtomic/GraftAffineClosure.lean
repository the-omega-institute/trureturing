import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
open _root_.D5.S3.Arith.Congruence.PrimePowerAffineBehavior (depth)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ H => H) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R :=
    (∀ (p h e : ℕ), p.Prime → e ≤ h → ∀ x y : ℤ,
      (∀ b : ℤ, Int.gcd (x + (p : ℤ) ^ e * b) ((p : ℤ) ^ h) =
        Int.gcd (y + (p : ℤ) ^ e * b) ((p : ℤ) ^ h)) ↔ psi p h e x = psi p h e y) ∧
    (∀ (p h e : ℕ), p.Prime → e ≤ h → ∀ x : ℤ,
      depth p h x ≤ h ∧ Int.gcd x ((p : ℤ) ^ h) = p ^ depth p h x ∧
        (depth p h x = h ↔ (p : ℤ) ^ h ∣ x) ∧
        (x ≠ 0 → depth p h x = min (padicValInt p x) h) ∧
        (e ≤ depth p h x ↔ (p : ℤ) ^ e ∣ x)) ∧
    (∀ (H : ℕ), 0 < H → ∀ w : ℕ × ℕ,
      (∀ W : List Bool, ∃ k : ℕ, ∃ t : ℕ × ℕ,
        residue H t ∈ graftSpace H w ∧ ∀ v : ℕ × ℕ,
          run w W v = step^[k] v + t) ∧
      (∀ v : ZMod H × ZMod H, step^[(H ^ 2).factorial] v = v) ∧
      (∀ k A B : ℕ, ∀ v : ℕ × ℕ,
        run w (realizationWord H k A B) v =
          step^[k + (H ^ 2).factorial] v +
            A • step^[(H ^ 2).factorial] w + B • step w) ∧
      (∀ k : ℕ, ∀ t ∈ graftSpace H w, ∃ W : List Bool,
        ∀ v : ℕ × ℕ, residue H (run w W v) = step^[k] (residue H v) + t) ∧
      (Nat.gcd (Nat.gcd (quantity w) (quantity (step w))) H = graftGcd H w) ∧
      (∀ z : ZMod H, (∃ t ∈ graftSpace H w, quantity t = z) ↔
        ∃ c : ZMod H, z = (graftGcd H w : ZMod H) * c) ∧
      (∀ v v' : ℕ × ℕ, behavior H w v v' ↔ ∀ (k : ℕ) (b : ℤ),
        Int.gcd (((quantity (step^[k] v) : ℕ) : ℤ) + graftGcd H w * b) H =
          Int.gcd (((quantity (step^[k] v') : ℕ) : ℤ) + graftGcd H w * b) H) ∧
      (∀ v v' : ℕ × ℕ, behavior H w v v' ↔ ∀ p : ℕ, p.Prime → p ∣ H → ∀ k : ℕ,
        psi p (H.factorization p) ((graftGcd H w).factorization p)
            ((quantity (step^[k] v) : ℕ) : ℤ) =
          psi p (H.factorization p) ((graftGcd H w).factorization p)
            ((quantity (step^[k] v') : ℕ) : ℤ)) ∧
      Function.Surjective (residue H) ∧
      (∀ x : ZMod H × ZMod H, ∃ v : ℕ × ℕ,
        v.1 < H ∧ v.2 < H ∧ residue H v = x) ∧
      Function.Surjective (fun v : ℕ × ℕ => observe (residue H v)) ∧
      (∀ v : ℕ × ℕ, observe v = step^[4] v ∧
        observe (step v) = step (observe v) ∧ observe (v + w) = observe v + observe w) ∧
      (∀ k : ℕ, ∀ v : ℕ × ℕ, (step^[k] (observe v)).1 = quantity (step^[k] v)) ∧
      Autonomous H w (residue H) step (fun v => v + residue H w) (residueReadout H) ∧
      Cardinal.mk (ZMod H × ZMod H) = (H ^ 2 : ℕ) ∧
      Cardinal.mk (Set.range (residue H)) = (H ^ 2 : ℕ) ∧
      (∀ v : ZMod H × ZMod H,
        observe (5 * v.1 - 3 * v.2, -3 * v.1 + 2 * v.2) = v) ∧
      matrixM ^ 4 = matrixC ∧ Matrix.det matrixM = -1 ∧ Matrix.det matrixC = 1 ∧
      matrixC * !![5, -3; -3, 2] = 1 ∧ matrixM ^ 2 = matrixM + 1 ∧
      (∀ t ∈ graftSpace H w, step t ∈ graftSpace H w ∧
        (t.2 - t.1, t.1) ∈ graftSpace H w) ∧
      (∀ k A B : ℕ, (realizationWord H k A B).length =
        (H ^ 2).factorial + k + A + B) ∧
      (graftGcd H w = H → ∀ (k : ℕ) (b : ℤ) (v : ℕ × ℕ),
        Int.gcd (((quantity (step^[k] v) : ℕ) : ℤ) + graftGcd H w * b) H =
          readout H (step^[k] v)) ∧
      (H = 1 → ∀ v : ℕ × ℕ, readout H v = 1) ∧
      (∀ j : ℕ, w = atomicBlock j →
        (quantity w = Nat.fib (j + 3) ∧ quantity (step w) = Nat.fib (j + 4)) ∧
        Nat.gcd w.1 w.2 = 1 ∧ graftGcd H w = 1 ∧
        (j = 0 → w = (1, 0)) ∧
        (0 < j → w = (Nat.fib (j - 1), Nat.fib j)) ∧
        blockMatrix j = matrixM ^ j ∧
        Nat.Coprime (quantity w) (quantity (step w)) ∧
        Matrix.det (blockMatrix j) = (-1 : ℤ) ^ j ∧
        (∀ v v' : ℕ × ℕ, behavior H w v v' ↔ residue H v = residue H v') ∧
        (∀ v v' : ℕ × ℕ, residue H v ≠ residue H v' →
          ∃ k A B : ℕ, k ≤ 1 ∧ A < H ∧ B < H ∧
            (w = (1, 0) → (A : ZMod H) = ((quantity (step^[k] v) : ℕ) : ZMod H) ∧
              (B : ZMod H) = -((quantity (step^[k] v) : ℕ) : ZMod H)) ∧
            (realizationWord H k A B).length ≤ (H ^ 2).factorial + 2 * (H - 1) + 1 ∧
            readout H (run w (realizationWord H k A B) v) = H ∧
            readout H (run w (realizationWord H k A B) v') < H) ∧
        (∀ (S : Type) (E : (ℕ × ℕ) → S) (δR δG : S → S) (o : S → ℕ),
          Autonomous H w E δR δG o → ((R.readout () () H) ^ 2 : ℕ) ≤ Cardinal.mk (Set.range E))))

theorem actual_law : arena.Law actual := result

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hglobal := h.2.2 1 Nat.zero_lt_one (atomicBlock 0)
  have hatomic := hglobal.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 rfl
  have hlower := hatomic.2.2.2.2.2.2.2.2.2.2
  have hauto : Autonomous 1 (atomicBlock 0) (fun _ => ()) (fun _ => ())
      (fun _ => ()) (fun _ => 1) := by
    refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
    intro v
    simp [readout]
  have impossible := hlower Unit (fun _ => ()) (fun _ => ()) (fun _ => ())
    (fun _ => 1) hauto
  norm_num [rejected, realize, Cardinal.mk_fintype] at impossible

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), 1, 2, by norm_num [actual, realize]⟩

register_information_theorem result in arena
  readout via (realize signature (fun _ _ H => H) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "body", "body", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body",
        "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0 }] })
  escape continues (open)

#print axioms registration
end Reg.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
