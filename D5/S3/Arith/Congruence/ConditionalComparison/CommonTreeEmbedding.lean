/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CommonTreeEmbedding
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ConditionalComparison/CommonTreeEmbedding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Naturally ranked common-tree embeddings are injective, exact and prefix coherent. -/

import D5.S3.Arith.Congruence.ConditionalComparison.CommonTreeUnion
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.Tuple.Take

namespace Erdos7.CommonTreeUnion

/-- Encode a source path by ranking the chosen target children at each visited node.
The recursive subtree is indexed by the resulting target digit. -/
def rankEncode {s r : ℕ} : {B : ℕ} → Tree s r B →
    {j : ℕ} → j ≤ B → Word r j → Word s j
  | _, _, 0, _, _ => Fin.elim0
  | 0, _, j + 1, h, _ => False.elim (by omega)
  | B + 1, Θ, j + 1, h, x =>
    let a := Θ.1.val.orderEmbOfFin Θ.1.property (x 0)
    Fin.cons a (rankEncode (Θ.2 a) (Nat.le_of_succ_le_succ h) (Fin.tail x))

/-- One sampled finite tree determines injective maps at every depth, whose full
image is exactly the independently defined selected leaves. All maps commute with
prefix truncation, and every finite union of native prefix-hit events is the hit
event of the union of their ambient full-depth extensions. -/
theorem rank_encode_coherent_and_exact {s r : ℕ} (_hr : 2 ≤ r) (_hrs : r < s)
    (B : ℕ) (Θ : Tree s r B) :
    (∀ (j : ℕ) (hj : j ≤ B), Function.Injective (rankEncode Θ hj)) ∧
    (∀ w : Word s B, selected B Θ w ↔
      ∃ x : Word r B, rankEncode Θ (le_refl B) x = w) ∧
    (∀ (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ B) (x : Word r k),
      rankEncode Θ (hjk.trans hk) (Fin.take j hjk x) =
        Fin.take j hjk (rankEncode Θ hk x)) ∧
    (∀ P : Finset (Σ d : Fin (B + 1), Prefix s d.val),
      (∃ p ∈ P, Hit Θ (fun w => HasPrefix w p.2 (Nat.le_of_lt_succ p.1.isLt))) ↔
        Hit Θ (fun w => ∃ p ∈ P, HasPrefix w p.2 (Nat.le_of_lt_succ p.1.isLt))) := by
  have invariant : ∀ (B : ℕ) (Θ : Tree s r B),
      (∀ (j : ℕ) (hj : j ≤ B), Function.Injective (rankEncode Θ hj)) ∧
      (∀ w : Word s B, selected B Θ w ↔
        ∃ x : Word r B, rankEncode Θ (le_refl B) x = w) ∧
      (∀ (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ B) (x : Word r k),
        rankEncode Θ (hjk.trans hk) (Fin.take j hjk x) =
          Fin.take j hjk (rankEncode Θ hk x)) := by
    intro B
    induction B with
    | zero =>
      intro Θ
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        subst j
        exact fun _ _ _ => Subsingleton.elim _ _
      · intro w
        exact ⟨fun _ => ⟨Fin.elim0, Subsingleton.elim _ _⟩, fun _ => trivial⟩
      · intro j k hjk hk x
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hjk
        subst j
        exact Subsingleton.elim _ _
    | succ B ih =>
      intro Θ
      let e := Θ.1.val.orderEmbOfFin Θ.1.property
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        cases j with
        | zero => exact fun _ _ _ => Subsingleton.elim _ _
        | succ j =>
          intro x y hxy
          have hhead : x 0 = y 0 := e.injective (by
            simpa only [rankEncode, Fin.cons_zero] using congrFun hxy 0)
          have htail : rankEncode (Θ.2 (e (x 0))) (Nat.le_of_succ_le_succ hj)
              (Fin.tail x) =
              rankEncode (Θ.2 (e (y 0))) (Nat.le_of_succ_le_succ hj) (Fin.tail y) := by
            simpa only [rankEncode, Fin.tail_cons] using congrArg Fin.tail hxy
          rw [← hhead] at htail
          have hsource := (ih (Θ.2 (e (x 0)))).1 j (Nat.le_of_succ_le_succ hj) htail
          calc
            x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
            _ = Fin.cons (y 0) (Fin.tail y) := by rw [hhead, hsource]
            _ = y := Fin.cons_self_tail y
      · intro w
        constructor
        · intro hw
          obtain ⟨hroot, hchild⟩ := hw
          let i := (Θ.1.val.orderIsoOfFin Θ.1.property).symm ⟨w 0, hroot⟩
          have hi : e i = w 0 := by
            exact congrArg Subtype.val
              ((Θ.1.val.orderIsoOfFin Θ.1.property).apply_symm_apply ⟨w 0, hroot⟩)
          obtain ⟨x, hx⟩ := ((ih (Θ.2 (w 0))).2.1 (Fin.tail w)).mp hchild
          refine ⟨Fin.cons i x, ?_⟩
          simp only [rankEncode, Fin.cons_zero, Fin.tail_cons]
          change Fin.cons (e i) (rankEncode (Θ.2 (e i)) (le_refl B) x) = w
          rw [hi, hx]
          exact Fin.cons_self_tail w
        · rintro ⟨x, rfl⟩
          change e (x 0) ∈ Θ.1.val ∧
            selected B (Θ.2 (e (x 0)))
              (rankEncode (Θ.2 (e (x 0))) (le_refl B) (Fin.tail x))
          exact ⟨Θ.1.val.orderEmbOfFin_mem Θ.1.property (x 0),
            ((ih (Θ.2 (e (x 0)))).2.1 _).mpr ⟨Fin.tail x, rfl⟩⟩
      · intro j k hjk hk x
        cases j with
        | zero => exact Subsingleton.elim _ _
        | succ j =>
          cases k with
          | zero => omega
          | succ k =>
            have hjk' : j ≤ k := Nat.le_of_succ_le_succ hjk
            have hk' : k ≤ B := Nat.le_of_succ_le_succ hk
            have hchild := (ih (Θ.2 (e (x 0)))).2.2 j k hjk' hk' (Fin.tail x)
            funext i
            refine Fin.cases ?_ (fun t => ?_) i
            · rfl
            · change rankEncode (Θ.2 (e (x 0))) (hjk'.trans hk')
                (Fin.take j hjk' (Fin.tail x)) t =
                rankEncode (Θ.2 (e (x 0))) hk' (Fin.tail x) (Fin.castLE hjk' t)
              exact congrFun hchild t
  obtain ⟨hI, hX, hC⟩ := invariant B Θ
  refine ⟨hI, hX, hC, ?_⟩
  intro P
  constructor
  · rintro ⟨p, hp, w, hw, hs⟩
    exact ⟨w, ⟨p, hp, hw⟩, hs⟩
  · rintro ⟨w, ⟨p, hp, hw⟩, hs⟩
    exact ⟨p, hp, w, hw, hs⟩

end Erdos7.CommonTreeUnion
