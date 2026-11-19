/- GID: D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid
   mirror-E: none(waiver:structural-combinatorics)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.labelled_eq_twentyFour; premises=D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.two_colour_obstruction
   digest: Literal two-defect king colourings and their colour normalization. -/
/-
admission_basis: open-problem-resolution (#30655; Proved)
escape_witness: two_colour_obstruction (the universal two-colour 2 by 3 obstruction,
  consumed by the unbounded normalization theorem through an injective graph embedding)
TwoDefect: proof_shape=bind-only; consumers=KingTwoGrid.L
L: proof_shape=bind-only; consumers=HardinA229753.result
T: proof_shape=bind-only; consumers=HardinA229753.result
embedCell: proof_shape=bind-only; consumers=mono_embed,twoDefect_usesThree_wide
embedEdge: proof_shape=bind-only; consumers=embedEdge_injective,mono_embed,
  twoDefect_usesThree_wide
embedEdge_injective: proof_shape=bind-only; consumers=twoDefect_usesThree_wide
mono_embed: proof_shape=bind-only; consumers=twoDefect_usesThree_wide
two_colour_factor: proof_shape=bind-only; consumers=twoDefect_usesThree_wide
two_colour_obstruction: proof_shape=content; consumers=twoDefect_usesThree_wide
twoDefect_usesThree_wide: proof_shape=content; consumers=twoDefect_usesThree
twoDefect_usesThree: proof_shape=content; consumers=labelled_eq_twentyFour
labelled_eq_twentyFour: proof_shape=content; consumers=HardinA229753.result
The global slot-count and settlement consumers remain separate obligations.
The universal normalization is reduced to the verified two-colour obstruction;
labelled_eq_twentyFour consumes it through twoDefect_usesThree_wide and twoDefect_usesThree.
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid

/-! Two equal bonds force three occurring colours except on the single 2 by 2 block. -/
namespace D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid

open D5.S3.StatisticalMechanics.Potts.KingDefects.KingGrid
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical

def TwoDefect {n k : ℕ} (f : Cell n k → Fin 4) : Prop :=
  (Finset.univ.filter (fun e : Edge n k => mono f e)).card = 2

noncomputable def L (n k : ℕ) : ℕ := Nat.card {f : Cell n k → Fin 4 // TwoDefect f}

noncomputable def T (n k : ℕ) : ℕ :=
  Nat.card {f : Cell n k → Fin 4 // TwoDefect f ∧ normal f}

private def embedCell {n k : ℕ} (hn : 2 ≤ n) (hk : 3 ≤ k) : Cell 2 3 → Cell n k :=
  fun p => (p.1.castLE hn, p.2.castLE hk)

private def embedEdge {n k : ℕ} (hn : 2 ≤ n) (hk : 3 ≤ k) : Edge 2 3 → Edge n k
  | .H i j => .H (i.castLE hn) (j.castLE (by omega))
  | .V i j => .V (i.castLE (by omega)) (j.castLE hk)
  | .D i j => .D (i.castLE (by omega)) (j.castLE (by omega))
  | .A i j => .A (i.castLE (by omega)) (j.castLE (by omega))

private theorem embedEdge_injective {n k : ℕ} (hn : 2 ≤ n) (hk : 3 ≤ k) :
    Function.Injective (embedEdge hn hk) := by
  intro e d h
  cases e <;> cases d <;> simp_all [embedEdge, Fin.ext_iff]

private theorem mono_embed {n k : ℕ} {C : Type*} (hn : 2 ≤ n) (hk : 3 ≤ k)
    (f : Cell n k → C) (e : Edge 2 3) :
    mono f (embedEdge hn hk e) ↔ mono (fun p => f (embedCell hn hk p)) e := by
  cases e <;> rfl

private theorem two_colour_factor {X : Type*} (f : X → Fin 4) (a : X)
    (hf : ¬ UsesThree f) : ∃ g : X → Bool, ∀ x y, f x = f y ↔ g x = g y := by
  classical
  by_cases hall : ∀ x, f x = f a
  · exact ⟨fun _ => false, fun x y => by simp [hall x, hall y]⟩
  push Not at hall
  obtain ⟨b, hb⟩ := hall
  have span (x : X) : f x = f a ∨ f x = f b := by
    by_contra h
    push Not at h
    exact hf ⟨a, b, x, Ne.symm hb, Ne.symm h.1, Ne.symm h.2⟩
  refine ⟨fun x => decide (f x = f a), fun x y => ?_⟩
  constructor
  · intro h
    change decide (f x = f a) = decide (f y = f a)
    rw [h]
  · intro h
    by_cases hx : f x = f a <;> by_cases hy : f y = f a
    · exact hx.trans hy.symm
    · simp [hx, hy] at h
    · simp [hx, hy] at h
    · exact ((span x).resolve_left hx).trans ((span y).resolve_left hy).symm

private theorem two_colour_obstruction (f : Cell 2 3 → Bool) :
    3 ≤ (Finset.univ.filter (fun e : Edge 2 3 => mono f e)).card := by
  revert f
  decide

private theorem twoDefect_usesThree_wide {n k : ℕ} (hn : 2 ≤ n) (hk : 3 ≤ k)
    (f : Cell n k → Fin 4) (hf : TwoDefect f) : UsesThree f := by
  classical
  by_contra hthree
  obtain ⟨g, hg⟩ := two_colour_factor f (⟨0, by omega⟩, ⟨0, by omega⟩) hthree
  let A : Finset (Edge 2 3) :=
    Finset.univ.filter (fun e => mono (fun p => g (embedCell hn hk p)) e)
  have hA : 3 ≤ A.card := two_colour_obstruction (fun p => g (embedCell hn hk p))
  have hsub : A.image (embedEdge hn hk) ⊆ Finset.univ.filter (fun e => mono f e) := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (mono_embed hn hk f e).mpr ?_⟩
    exact (hg _ _).mpr (Finset.mem_filter.mp he).2
  have hle : A.card ≤ (Finset.univ.filter (fun e => mono f e)).card := by
    calc
      A.card = (A.image (embedEdge hn hk)).card :=
        (Finset.card_image_of_injective A (embedEdge_injective hn hk)).symm
      _ ≤ _ := Finset.card_le_card hsub
  unfold TwoDefect at hf
  omega

private theorem twoDefect_usesThree {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k)
    (hne : n ≠ 2 ∨ k ≠ 2) (f : Cell n k → Fin 4) (hf : TwoDefect f) : UsesThree f := by
  by_cases hk3 : 3 ≤ k
  · exact twoDefect_usesThree_wide hn hk3 f hf
  have hn3 : 3 ≤ n := by omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := twoDefect_usesThree_wide hk hn3 (transpose f)
    (by
      classical
      have hc := Nat.card_congr (transposeEdge.subtypeEquiv
        (p := fun e => mono f e) (q := fun e => mono (transpose f) e)
        (fun e => (transpose_mono f e).symm))
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
      simpa only [TwoDefect, ← hc] using hf)
  exact ⟨a.swap, b.swap, c.swap, hab, hac, hbc⟩

/-- Three occurring colours make the colour-permutation action free. -/
theorem labelled_eq_twentyFour (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k)
    (hne : n ≠ 2 ∨ k ≠ 2) : L n k = 24 * T n k := by
  classical
  let E : (Cell n k → Fin 4) ≃ (Fin (n * k) → Fin 4) :=
    Equiv.arrowCongr finProdFinEquiv (Equiv.refl _)
  let S : (Fin (n * k) → Fin 4) → Prop := fun w => TwoDefect (E.symm w)
  have hinv : ∀ p : Equiv.Perm (Fin 4), ∀ w, S (p ∘ w) ↔ S w := by
    intro p w
    change TwoDefect (fun v => p (w (finProdFinEquiv v))) ↔
      TwoDefect (fun v => w (finProdFinEquiv v))
    simp only [TwoDefect, mono, p.injective.eq_iff]
  have hthree : ∀ w, S w → UsesThree w := by
    intro w hw
    obtain ⟨a, b, c, hab, hac, hbc⟩ := twoDefect_usesThree hn hk hne (E.symm w) hw
    exact ⟨finProdFinEquiv a, finProdFinEquiv b, finProdFinEquiv c, hab, hac, hbc⟩
  have eL := E.subtypeEquiv (p := fun f => TwoDefect f) (q := S) (by
    intro f
    change TwoDefect f ↔ TwoDefect (E.symm (E f))
    rw [E.symm_apply_apply])
  have eT := E.subtypeEquiv
    (p := fun f => TwoDefect f ∧ normal f) (q := fun w => S w ∧ Canonical w) (by
      intro f
      change (TwoDefect f ∧ Canonical (E f)) ↔
        (TwoDefect (E.symm (E f)) ∧ Canonical (E f))
      rw [E.symm_apply_apply])
  unfold L T
  rw [Nat.card_congr eL, Nat.card_congr eT]
  exact canonical_count_three S hinv hthree

end D5.S3.StatisticalMechanics.Potts.KingDefects.KingTwoGrid
