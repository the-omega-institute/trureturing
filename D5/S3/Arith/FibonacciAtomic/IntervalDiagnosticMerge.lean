/- GID: D5/S3/Arith/FibonacciAtomic/IntervalDiagnosticMerge
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/IntervalDiagnosticMerge
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Interval messages retain the first internal failure and incoming bit. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import D5.S3.Arith.FibonacciAtomic.TreeMessageRealization
import D5.S3.Arith.FibonacciAtomic.FourMessageTreeRigidity

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.IntervalDiagnosticMerge

open LiteralWindowEnd (Window first last)
open FirstRejectionCutCapacity (Word Label bad task interval)
open TreeMessageRealization (leaf fork leaves Full subtrees Implementation evaluate)

/-- Failed messages retain their incoming bit, but have no outgoing field. -/
inductive Msg (k : ℕ)
  | failed (position : Fin (k + 1)) (incoming : Bool)
  | live (incoming outgoing : Bool)
  deriving DecidableEq

def incoming {k : ℕ} : Msg k → Bool
  | .failed _ u => u
  | .live u _ => u

/-- Half-open adjacent blocks, with no constraint on the binary tree's shape. -/
inductive Ordered (k : ℕ) : ℕ → ℕ → TreeMessageRealization.Tree (Fin (k + 1)) → Prop
  | leaf (i : Fin (k + 1)) : Ordered k i.val (i.val + 1) (leaf i)
  | fork {a b c : ℕ} {L R : TreeMessageRealization.Tree (Fin (k + 1))}
      (hab : a < b) (hbc : b < c) (hc : c ≤ k + 1)
      (left : Ordered k a b L) (right : Ordered k b c R) :
      Ordered k a c (fork L R)

/-- The last coordinate in a left child identifies its seam with the right child. -/
noncomputable def seam {k : ℕ} (L : TreeMessageRealization.Tree (Fin (k + 1))) : Fin (k + 1) :=
  ⟨min ((leaves L).sup Fin.val) k, by omega⟩

/-- Four syntax rules. The merger reads messages and a seam coordinate only. -/
def combine {k : ℕ} (j : Fin (k + 1)) : Msg k → Msg k → Msg k
  | .failed f u, _ => .failed f u
  | .live u v, q =>
      if v = true ∧ incoming q = true then .failed j u else
        match q with
        | .failed f _ => .failed f u
        | .live _ z => .live u z

def encode {k : ℕ} (i : Fin (k + 1)) (x : Window) : Msg k :=
  .live (if i.val = 0 then false else first x)
    (if i.val = k then decide (x = .zero) else last x)

noncomputable def implementation (k : ℕ) : Implementation (fun _ : Fin (k + 1) => Window) where
  Message := fun _ => Msg k
  empty := .live false false
  encode := fun i _ _ => encode i
  combine := fun L _ => combine (seam L)

def read {k : ℕ} : Msg k → Label k
  | .failed f _ => f
  | .live _ z => if z then (Fin.last k : Label k) else ⊤

/-- Boundary fields are defined from the original word independently of the merger. -/
def leftBit {k : ℕ} (a : ℕ) (w : Word k) : Bool :=
  if a = 0 then false else first (w ⟨min a k, by omega⟩)

def rightBit {k : ℕ} (b : ℕ) (w : Word k) : Bool :=
  if b = k + 1 then decide (w (Fin.last k) = .zero)
  else last (w ⟨min (b - 1) k, by omega⟩)

/-- The declarative message meaning: the first bad internal seam, or absence
of internal bad seams together with the two boundary fields. Terminal zero
is a boundary flag and never an internal failure. -/
def Semantics {k : ℕ} (a b : ℕ) (w : Word k) : Msg k → Prop
  | .failed f u => u = leftBit a w ∧ a ≤ f.val ∧ f.val + 1 < b ∧ bad w f ∧
      ∀ i : Fin (k + 1), a ≤ i.val → i.val < f.val → ¬ bad w i
  | .live u z => u = leftBit a w ∧ z = rightBit b w ∧
      ∀ i : Fin (k + 1), a ≤ i.val → i.val + 1 < b → ¬ bad w i

/-- Every ordered interval tree computes exactly its declarative diagnostic
message at every node. At the full root its readout is the first rejection task. -/
theorem result (k : ℕ) (t : TreeMessageRealization.Tree (Fin (k + 1)))
    (ht : Ordered k 0 (k + 1) t) (w : Word k) :
    Full t ∧ leaves t = Finset.univ ∧
      (∀ s ∈ subtrees t, ∃ a b : ℕ, a < b ∧ b ≤ k + 1 ∧
        leaves s = interval k a b ∧
        ∀ m : Msg k, Semantics a b w m ↔ m = evaluate (implementation k) s w) ∧
      read (evaluate (implementation k) t w) = task w := by
  classical
  have merge_sound (a b c : ℕ) (j : Fin (k + 1))
      (hab : a < b) (hbc : b < c) (hc : c ≤ k + 1) (hj : j.val + 1 = b)
      (p q : Msg k) (hp : Semantics a b w p) (hq : Semantics b c w q) :
      Semantics a c w (combine j p q) := by
    have cross : bad w j ↔ rightBit b w = true ∧ leftBit b w = true := by
      have hjk : j.val < k := by omega
      have hb0 : b ≠ 0 := by omega
      have hbn : b ≠ k + 1 := by omega
      have hlast : (⟨min (b - 1) k, by omega⟩ : Fin (k + 1)) = j := by
        apply Fin.ext
        dsimp
        omega
      have hfirst : (⟨min b k, by omega⟩ : Fin (k + 1)) =
          ⟨j.val + 1, by omega⟩ := by
        apply Fin.ext
        dsimp
        omega
      simp only [bad, dif_pos hjk, rightBit, if_neg hbn, leftBit, if_neg hb0]
      rw [hlast, hfirst]
    cases p with
    | failed f u =>
        change Semantics a c w (.failed f u)
        rcases hp with ⟨hu, haf, hfb, hf, hprior⟩
        exact ⟨hu, haf, by omega, hf, hprior⟩
    | live u v =>
        rcases hp with ⟨hu, hv, hsafeL⟩
        have hqu : incoming q = leftBit b w := by
          cases q <;> exact hq.1
        by_cases hbad : v = true ∧ incoming q = true
        · have hjbad : bad w j := cross.mpr (by simpa [hv, hqu] using hbad)
          simp only [combine, if_pos hbad]
          refine ⟨hu, by omega, by omega, hjbad, ?_⟩
          intro i hai hij
          exact hsafeL i hai (by omega)
        · have hjgood : ¬ bad w j := by
            intro h
            exact hbad (by simpa [hv, hqu] using cross.mp h)
          have no_seam (i : Fin (k + 1)) (hib : i.val + 1 = b) : ¬ bad w i := by
            have he : i = j := Fin.ext (by omega)
            simpa [he] using hjgood
          cases q with
          | failed f v' =>
              rcases hq with ⟨_, hbf, hfc, hf, hprior⟩
              simp only [combine, if_neg hbad]
              refine ⟨hu, by omega, hfc, hf, ?_⟩
              intro i hai hif
              by_cases hib : i.val + 1 < b
              · exact hsafeL i hai hib
              · by_cases hie : i.val + 1 = b
                · exact no_seam i hie
                · exact hprior i (by omega) hif
          | live v' z =>
              rcases hq with ⟨_, hz, hsafeR⟩
              simp only [combine, if_neg hbad]
              refine ⟨hu, hz, ?_⟩
              intro i hai hic
              by_cases hib : i.val + 1 < b
              · exact hsafeL i hai hib
              · by_cases hie : i.val + 1 = b
                · exact no_seam i hie
                · exact hsafeR i (by omega) hic
  have unique (a b : ℕ) (p q : Msg k)
      (hp : Semantics a b w p) (hq : Semantics a b w q) : p = q := by
    cases p with
    | failed f u =>
        rcases hp with ⟨hu, haf, hfb, hf, hprior⟩
        cases q with
        | failed g v =>
            rcases hq with ⟨hv, hag, hgb, hg, hprior'⟩
            have hfg : f = g := by
              apply Fin.ext
              by_contra h
              rcases lt_or_gt_of_ne h with hlt | hgt
              · exact hprior' f haf hlt hf
              · exact hprior g hag hgt hg
            simp [hfg, hu, hv]
        | live v z => exact False.elim (hq.2.2 f haf hfb hf)
    | live u z =>
        cases q with
        | failed f v => exact False.elim (hp.2.2 f hq.2.1 hq.2.2.1 hq.2.2.2.1)
        | live v z' => simp [hp.1, hq.1, hp.2.1, hq.2.1]
  have build (a b : ℕ) (s : TreeMessageRealization.Tree (Fin (k + 1))) (hs : Ordered k a b s) :
      a < b ∧ b ≤ k + 1 ∧ Full s ∧ leaves s = interval k a b ∧
        Semantics a b w (evaluate (implementation k) s w) ∧
        ∀ r ∈ subtrees s, ∃ c d : ℕ, c < d ∧ d ≤ k + 1 ∧
          leaves r = interval k c d ∧ Semantics c d w (evaluate (implementation k) r w) := by
    induction hs with
    | leaf i =>
        have hs : Semantics i.val (i.val + 1) w (encode i (w i)) := by
          have hleft : leftBit i.val w = if i.val = 0 then false else first (w i) := by
            unfold leftBit
            congr 1
            have hi : (⟨min i.val k, by omega⟩ : Fin (k + 1)) = i := by
              apply Fin.ext
              dsimp
              omega
            rw [hi]
          have hright : rightBit (i.val + 1) w =
              if i.val = k then decide (w i = .zero) else last (w i) := by
            by_cases hik : i.val = k
            · have he : i = Fin.last k := Fin.ext hik
              simp [rightBit, he]
            · have hi : (⟨min (i.val + 1 - 1) k, by omega⟩ : Fin (k + 1)) = i := by
                apply Fin.ext
                dsimp
                omega
              simp only [rightBit, if_neg (by omega : i.val + 1 ≠ k + 1), if_neg hik]
              rw [hi]
          change _ = _ ∧ _ = _ ∧ _
          refine ⟨hleft.symm, hright.symm, ?_⟩
          intro j hj hj'
          omega
        have hleaf := FirstRejectionCutCapacity.singleton_interval k i
        refine ⟨by omega, by omega, by simp [Full], hleaf, hs, ?_⟩
        intro r hr
        have he : r = leaf i := by simpa [subtrees] using hr
        subst r
        exact ⟨i.val, i.val + 1, by omega, by omega, hleaf, hs⟩
    | @fork a b c L R hab hbc hc hL hR ihL ihR =>
        rcases ihL with ⟨_, _, hLf, hLa, hLs, hLd⟩
        rcases ihR with ⟨_, _, hRf, hRa, hRs, hRd⟩
        have hdis : Disjoint (leaves L) (leaves R) := by
          rw [hLa, hRa]
          apply Finset.disjoint_left.mpr
          intro i hi hi'
          simp only [interval, Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
          omega
        have hleaves : leaves (fork L R) = interval k a c := by
          simp only [leaves, hLa, hRa]
          ext i
          simp only [Finset.mem_union, interval, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        have hseam : (seam L).val + 1 = b := by
          have upper : (leaves L).sup Fin.val ≤ b - 1 := by
            apply Finset.sup_le
            intro i hi
            rw [hLa] at hi
            simp only [interval, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            omega
          let i : Fin (k + 1) := ⟨b - 1, by omega⟩
          have hi : i ∈ leaves L := by
            rw [hLa]
            simp only [interval, Finset.mem_filter, Finset.mem_univ, true_and]
            dsimp [i]
            omega
          have lower := Finset.le_sup (f := Fin.val) hi
          dsimp [i] at lower
          dsimp [seam]
          omega
        have hmerged : Semantics a c w (evaluate (implementation k) (fork L R) w) :=
          merge_sound a b c (seam L) hab hbc hc hseam _ _ hLs hRs
        refine ⟨by omega, hc, ⟨hLf, hRf, hdis⟩, hleaves, hmerged, ?_⟩
        intro r hr
        simp only [subtrees, Finset.mem_insert, Finset.mem_union] at hr
        rcases hr with rfl | hr | hr
        · exact ⟨a, c, by omega, hc, hleaves, hmerged⟩
        · exact hLd r hr
        · exact hRd r hr
  have least (f : Fin (k + 1)) (hf : bad w f)
      (hsafe : ∀ i : Fin (k + 1), i.val < f.val → ¬ bad w i) :
      task w = (f : Label k) := by
    apply le_antisymm
    · unfold task
      exact (Finset.inf_le (Finset.mem_univ f)).trans (by simp [hf])
    · unfold task
      apply Finset.le_inf
      intro i _
      by_cases hi : bad w i
      · simp only [if_pos hi, WithTop.coe_le_coe]
        change f.val ≤ i.val
        by_contra h
        exact hsafe i (by omega) hi
      · simp [hi]
  have root_sound (m : Msg k) (hm : Semantics 0 (k + 1) w m) : read m = task w := by
    cases m with
    | failed f u =>
        exact (least f hm.2.2.2.1 (fun i hi => hm.2.2.2.2 i (by omega) hi)).symm
    | live u z =>
        have hz : z = decide (w (Fin.last k) = .zero) := by
          simpa [rightBit] using hm.2.1
        by_cases hlast : w (Fin.last k) = .zero
        · have hf : bad w (Fin.last k) := by simp [bad, hlast]
          have htask := least (Fin.last k) hf (fun i hi => hm.2.2 i (by omega) (by
            simp only [Fin.val_last] at hi
            omega))
          simp [read, hz, hlast, htask]
        · have htask : task w = ⊤ := by
            apply le_antisymm le_top
            unfold task
            apply Finset.le_inf
            intro i _
            have hi : ¬ bad w i := by
              by_cases hik : i.val < k
              · exact hm.2.2 i (by omega) (by omega)
              · have he : i = Fin.last k := Fin.ext (by simp only [Fin.val_last]; omega)
                simp [he, bad, hlast]
            simp [hi]
          simp [read, hz, hlast, htask]
  obtain ⟨_, _, hfull, hleaves, hsem, hdesc⟩ := build 0 (k + 1) t ht
  have hall : interval k 0 (k + 1) = Finset.univ :=
    (FourMessageTreeRigidity.univ_interval k).symm
  refine ⟨hfull, hleaves.trans hall, ?_, root_sound _ hsem⟩
  intro s hs
  obtain ⟨a, b, hab, hb, hleaves, hsem⟩ := hdesc s hs
  refine ⟨a, b, hab, hb, hleaves, ?_⟩
  intro m
  exact ⟨fun hm => unique a b m _ hm hsem, fun he => he.symm ▸ hsem⟩

end D5.S3.Arith.FibonacciAtomic.IntervalDiagnosticMerge
