/- GID: D5/S3/Combinatorics/Graph/Domination/FiniteLinePrefixCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Domination/FiniteLinePrefixCount
   mirror-E: none(waiver:uniform-finite-branching)
   anchors: [mathlib/module/Mathlib.Data.Fintype.BigOperators]
   utility: none
   digest: Uniform extension counts on actual finite tuples with distinct column labels. -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Combinatorics.Graph.Domination.FiniteLinePrefixCount

open Finset
open scoped BigOperators

variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

/-- Tuples on the first k prescribed lines, with distinct column labels. -/
def Prefix (line : ℕ → Finset V) (column : V → W) (k : ℕ) :=
  {f : Fin k → V // (∀ i, f i ∈ line i.val) ∧ Function.Injective (column ∘ f)}

instance (line : ℕ → Finset V) (column : V → W) (k : ℕ) :
    Fintype (Prefix line column k) := by
  classical
  unfold Prefix
  infer_instance

/-- The legal next vertices over this particular tuple. -/
def Options (line : ℕ → Finset V) (column : V → W) {k : ℕ}
    (p : Prefix line column k) :=
  {x : V // x ∈ line k ∧ ∀ i, column x ≠ column (p.val i)}

instance (line : ℕ → Finset V) (column : V → W) {k : ℕ}
    (p : Prefix line column k) : Fintype (Options line column p) := by
  classical
  unfold Options
  infer_instance

private theorem options_card (line : ℕ → Finset V) (column : V → W)
    (hinj : ∀ k, Set.InjOn column (line k)) {m k : ℕ}
    (hlen : m + k ≤ (line k).card) (p : Prefix line column k) :
    m ≤ Fintype.card (Options line column p) := by
  classical
  let used : Finset W := univ.image (column ∘ p.val)
  let bad := (line k).filter (fun x => column x ∈ used)
  have hb : bad.card ≤ k := by
    calc
      bad.card ≤ used.card := Finset.card_le_card_of_injOn column
        (by intro x hx; exact (mem_filter.mp hx).2)
        (by intro x hx y hy h; exact hinj k (mem_filter.mp hx).1 (mem_filter.mp hy).1 h)
      _ ≤ k := by simpa [used] using (card_image_le (s := (univ : Finset (Fin k))) (f := column ∘ p.val))
  have hsplit := (card_filter_add_card_filter_not (s := line k) (fun x => column x ∈ used))
  have hc : Fintype.card (Options line column p) =
      ((line k).filter (fun x => column x ∉ used)).card := by
    apply Fintype.card_of_subtype
    intro x
    simp [Options, used, Function.comp_def]
  rw [hc]
  dsimp [bad] at hb
  omega

private def append (line : ℕ → Finset V) (column : V → W) {k : ℕ}
    (p : Prefix line column k) (x : Options line column p) : Prefix line column (k + 1) := by
  refine ⟨Fin.snoc p.val x.val, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using x.property.1
    · simpa using p.property.1 j
  · rw [Fin.comp_snoc]
    apply Fin.snoc_injective_of_injective p.property.2
    rintro ⟨i, hi⟩
    exact x.property.2 i hi.symm

private theorem append_injective (line : ℕ → Finset V) (column : V → W) (k : ℕ) :
    Function.Injective (fun q : (p : Prefix line column k) × Options line column p =>
      append line column q.1 q.2) := by
  rintro ⟨p, x⟩ ⟨q, y⟩ h
  have he := congrArg Subtype.val h
  have hp : p = q := by
    apply Subtype.ext
    funext i
    have := congrFun he i.castSucc
    simpa only [append, Fin.snoc_castSucc] using this
  subst q
  have hx : x = y := by
    apply Subtype.ext
    have := congrFun he (Fin.last k)
    simpa only [append, Fin.snoc_last] using this
  subst y
  rfl

/-- A uniform lower bound applies at every prefix, so choices can be multiplied. -/
theorem card_prefix_lower_bound (line : ℕ → Finset V) (column : V → W)
    (hinj : ∀ k, Set.InjOn column (line k)) (m K : ℕ)
    (hlen : ∀ k < K, m + k ≤ (line k).card) :
    m ^ K ≤ Fintype.card (Prefix line column K) := by
  classical
  have all : ∀ k, k ≤ K → m ^ k ≤ Fintype.card (Prefix line column k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have : Nonempty (Prefix line column 0) :=
        ⟨⟨Fin.elim0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩⟩
      simpa using (Fintype.card_pos_iff.mpr this)
    | succ k ih =>
      intro hk
      calc
        m ^ (k + 1) = m ^ k * m := pow_succ _ _
        _ ≤ Fintype.card (Prefix line column k) * m := Nat.mul_le_mul_right m (ih (by omega))
        _ = ∑ _p : Prefix line column k, m := by simp
        _ ≤ ∑ p : Prefix line column k, Fintype.card (Options line column p) := by
          apply Finset.sum_le_sum
          intro p _
          exact options_card line column hinj (hlen k (by omega)) p
        _ = Fintype.card ((p : Prefix line column k) × Options line column p) :=
          (Fintype.card_sigma _).symm
        _ ≤ Fintype.card (Prefix line column (k + 1)) :=
          Fintype.card_le_of_injective _ (append_injective line column k)
  exact all K le_rfl

end D5.S3.Combinatorics.Graph.Domination.FiniteLinePrefixCount
