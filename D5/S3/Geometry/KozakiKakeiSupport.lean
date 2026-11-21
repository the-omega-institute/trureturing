/- GID: D5/S3/Geometry/KozakiKakeiSupport
   generality: G
   mirror-B: D5/B/S3/Geometry/KozakiKakeiSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Boolean support counts of the signed matching equation distinguish cycle edges. -/
import D5.S3.Geometry.KozakiKakeiConstantBridge
import D5.S3.Geometry.KozakiKakeiCycle
import Mathlib.Data.Fintype.BigOperators

namespace D5.S3.Geometry.KozakiKakei
open MvPolynomial
open scoped BigOperators
noncomputable section

def boolNumber (b : Bool) : ℂ := if b then 1 else 0

def Cuts {m : ℕ} (M : Fin m × Bool ≃ Col m) (f : Col m → Bool) : Prop :=
  ∀ e, f (M (e, false)) ≠ f (M (e, true))

theorem eval_matching_ne_zero {m : ℕ} (M : Fin m × Bool ≃ Col m) (f : Col m → Bool) :
    eval (boolNumber ∘ f) (matchingPolynomial M) ≠ 0 ↔ Cuts M f := by
  have h : Function.Injective boolNumber := by
    intro b c heq
    cases b <;> cases c <;> simp_all [boolNumber]
  simp only [eval_matchingPolynomial, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies,
    Function.comp_apply, sub_ne_zero, h.ne_iff, Cuts]
  exact forall_congr' fun _ => ne_comm

private def colorFromBits {m : ℕ} (M : Fin m × Bool ≃ Col m) (g : Fin m → Bool)
    (v : Col m) : Bool :=
  (g (M.symm v).1) ^^ (M.symm v).2

private theorem colorFromBits_true {m : ℕ} (M : Fin m × Bool ≃ Col m) (g : Fin m → Bool)
    (v : Col m) :
    colorFromBits M g v = true ↔ g (M.symm v).1 = !(M.symm v).2 := by
  unfold colorFromBits
  cases g (M.symm v).1 <;> cases (M.symm v).2 <;> decide

private theorem colorFromBits_cuts {m : ℕ} (M : Fin m × Bool ≃ Col m) (g : Fin m → Bool) :
    Cuts M (colorFromBits M g) := by
  intro e
  simp [colorFromBits]

private theorem colorFromBits_of_cuts {m : ℕ} (M : Fin m × Bool ≃ Col m)
    (f : Col m → Bool) (hf : Cuts M f) :
    colorFromBits M (fun e => f (M (e, false))) = f := by
  funext v
  obtain ⟨⟨e, b⟩, rfl⟩ := M.surjective v
  cases b
  · simp [colorFromBits]
  · have h := hf e
    simp [colorFromBits]
    cases h₁ : f (M (e, false)) <;> cases h₂ : f (M (e, true)) <;> simp_all

private def cutSet {m : ℕ} (M : Fin m × Bool ≃ Col m) (i j : Col m) :
    Finset (Col m → Bool) := by
  classical exact Finset.univ.filter (fun f => f i = true ∧ f j = true ∧ Cuts M f)

private theorem mem_cutSet {m : ℕ} {M : Fin m × Bool ≃ Col m} {i j : Col m} {f : Col m → Bool} :
    f ∈ cutSet M i j ↔ f i = true ∧ f j = true ∧ Cuts M f := by
  classical simp [cutSet]

private theorem cutSet_sameEdge {m : ℕ} {M : Fin m × Bool ≃ Col m} {i j : Col m}
    (hn : i ≠ j) (h : SameEdge M i j) : cutSet M i j = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨hi, hj, hc⟩ := mem_cutSet.mp hf
  obtain ⟨e, he | he⟩ := (sameEdge_iff hn).mp h
  · exact hc e ((he.1 ▸ hi).trans (he.2 ▸ hj).symm)
  · exact hc e ((he.2 ▸ hj).trans (he.1 ▸ hi).symm)

private theorem fixed_bits_card {m : ℕ} {a b : Fin m} (hab : a ≠ b) (x y : Bool) :
    (Finset.univ.filter (fun g : Fin m → Bool => g a = x ∧ g b = y)).card = 2 ^ (m - 2) := by
  classical
  let pieces (i : Fin m) : Finset Bool :=
    if i = a then {x} else if i = b then {y} else Finset.univ
  have hp : (Finset.univ.filter (fun g : Fin m → Bool => g a = x ∧ g b = y)) =
      Fintype.piFinset pieces := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨ha, hb⟩ i
      by_cases hi : i = a
      · subst i
        simp [pieces, ha]
      · by_cases hj : i = b
        · subst i
          simp [pieces, hi, hb]
        · simp [pieces, hi, hj]
    · intro h
      exact ⟨by simpa [pieces] using h a, by simpa [pieces, hab.symm] using h b⟩
  rw [hp, Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
  have ha : (pieces a).card = 1 := by simp [pieces]
  have hb : (pieces b).card = 1 := by simp [pieces, hab.symm]
  rw [ha, hb, one_mul, one_mul]
  have hp' (i : Fin m) (hi : i ∈ (Finset.univ.erase a).erase b) :
      (pieces i).card = 2 := by
    obtain ⟨hib, hia⟩ := Finset.mem_erase.mp hi
    simp [pieces, hib, (Finset.mem_erase.mp hia).1]
  rw [Finset.prod_congr rfl hp', Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
    Finset.card_erase_of_mem (Finset.mem_univ a)]
  simp [Nat.sub_sub]

private theorem cutSet_distinctEdges {m : ℕ} {M : Fin m × Bool ≃ Col m} {i j : Col m}
    (h : ¬ SameEdge M i j) : (cutSet M i j).card = 2 ^ (m - 2) := by
  classical
  rw [← fixed_bits_card (show (M.symm i).1 ≠ (M.symm j).1 from h) (!(M.symm i).2) (!(M.symm j).2)]
  refine Finset.card_bij' (fun f _ e => f (M (e, false))) (fun g _ => colorFromBits M g) ?_ ?_ ?_ ?_
  · intro f hf
    obtain ⟨hi, hj, hc⟩ := mem_cutSet.mp hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have heq := colorFromBits_of_cuts M f hc
    exact ⟨(colorFromBits_true M _ i).mp (heq.symm ▸ hi),
      (colorFromBits_true M _ j).mp (heq.symm ▸ hj)⟩
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    exact mem_cutSet.mpr ⟨(colorFromBits_true M _ _).mpr hg.1,
      (colorFromBits_true M _ _).mpr hg.2, colorFromBits_cuts M g⟩
  · intro f hf
    exact colorFromBits_of_cuts M f (mem_cutSet.mp hf).2.2
  · intro g _
    funext e
    simp [colorFromBits]

theorem cuts_separate {m : ℕ} {M : Fin m × Bool ≃ Col m} {i j : Col m} {f : Col m → Bool}
    (hf : Cuts M f) (hn : i ≠ j) (he : SameEdge M i j) : f i ≠ f j := by
  obtain ⟨e, h | h⟩ := (sameEdge_iff hn).mp he
  · rw [h.1, h.2]
    exact hf e
  · rw [h.1, h.2]
    exact (hf e).symm

private theorem joint_agree {m : ℕ} (hm : 2 ≤ m) {i : Col m} {f g : Col m → Bool}
    (fo : Cuts (oddMatching m) f) (fe : Cuts (evenMatching m) f)
    (go : Cuts (oddMatching m) g) (ge : Cuts (evenMatching m) g)
    (hi : f i = g i) : f = g := by
  have hsep (t : Col m → Bool) (ho : Cuts (oddMatching m) t) (he : Cuts (evenMatching m) t)
      (v : Col m) : t v ≠ t (step hm v) := by
    have hn := (step_ne hm v).symm
    rcases (edges_cover hm hn).mp (Or.inl rfl) with h | h
    · exact cuts_separate ho hn h
    · exact cuts_separate he hn h
  have local_eq (v : Col m) : f v = g v ↔ f (step hm v) = g (step hm v) := by
    have hf := hsep f fo fe v
    have hg := hsep g go ge v
    cases h₁ : f v <;> cases h₂ : g v <;>
      cases h₃ : f (step hm v) <;> cases h₄ : g (step hm v) <;> simp_all
  have reach : ∀ (k : ℕ) (hk : k < 2*m),
      (f (first hm) = g (first hm) ↔ f ⟨k, hk⟩ = g ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      rfl
    | succ k ih =>
      intro hk
      have he : step hm ⟨k, by omega⟩ = ⟨k + 1, hk⟩ := by
        apply Fin.ext
        rw [step_val, ite_eq_left hk]
      exact (ih (by omega)).trans (by simpa only [he] using local_eq ⟨k, by omega⟩)
  have hfirst := (reach i.val i.isLt).mpr hi
  funext v
  exact (reach v.val v.isLt).mp hfirst

private theorem joint_card_le_one {m : ℕ} (hm : 2 ≤ m) (i j : Col m) :
    ((cutSet (oddMatching m) i j) ∩ (cutSet (evenMatching m) i j)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro f hf g hg
  obtain ⟨hfo, hfe⟩ := Finset.mem_inter.mp hf
  obtain ⟨hgo, hge⟩ := Finset.mem_inter.mp hg
  exact joint_agree hm (mem_cutSet.mp hfo).2.2 (mem_cutSet.mp hfe).2.2
    (mem_cutSet.mp hgo).2.2 (mem_cutSet.mp hge).2.2
    ((mem_cutSet.mp hfo).1.trans (mem_cutSet.mp hgo).1.symm)

private def pairSupport {m : ℕ} (i j : Col m) : Finset (Col m → Bool) := by
  classical
  exact Finset.univ.filter (fun f => f i = true ∧ f j = true ∧ eval (boolNumber ∘ f) (F m) ≠ 0)

private theorem mem_pairSupport {m : ℕ} {i j : Col m} {f : Col m → Bool} :
    f ∈ pairSupport i j ↔ f i = true ∧ f j = true ∧ eval (boolNumber ∘ f) (F m) ≠ 0 := by
  classical simp [pairSupport]

private theorem support_between {m : ℕ} (i j : Col m) :
    let O := cutSet (oddMatching m) i j
    let E := cutSet (evenMatching m) i j
    ((O ∪ E) \ (O ∩ E)) ⊆ pairSupport i j ∧ pairSupport i j ⊆ O ∪ E := by
  classical
  dsimp only
  constructor
  · intro f hf
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, mem_cutSet] at hf
    rcases hf.1 with ⟨hi, hj, ho⟩ | ⟨hi, hj, he⟩
    · have hE : ¬ Cuts (evenMatching m) f := fun h => hf.2 ⟨⟨hi, hj, ho⟩, ⟨hi, hj, h⟩⟩
      have ho' := (eval_matching_ne_zero _ _).mpr ho
      have he' := not_ne_iff.mp (mt (eval_matching_ne_zero _ _).mp hE)
      exact mem_pairSupport.mpr ⟨hi, hj, by simpa [F, he'] using ho'⟩
    · have hO : ¬ Cuts (oddMatching m) f := fun h => hf.2 ⟨⟨hi, hj, h⟩, ⟨hi, hj, he⟩⟩
      have he' := (eval_matching_ne_zero _ _).mpr he
      have ho' := not_ne_iff.mp (mt (eval_matching_ne_zero _ _).mp hO)
      exact mem_pairSupport.mpr ⟨hi, hj, by simpa [F, ho'] using he'⟩
  · intro f hf
    obtain ⟨hi, hj, h⟩ := mem_pairSupport.mp hf
    simp only [Finset.mem_union, mem_cutSet, hi, hj, true_and]
    by_contra hnone
    push Not at hnone
    have hO := not_ne_iff.mp (mt (eval_matching_ne_zero _ _).mp hnone.1)
    have hE := not_ne_iff.mp (mt (eval_matching_ne_zero _ _).mp hnone.2)
    apply h
    simp [F, hO, hE]

theorem signed_support_recovers_adjacency {m : ℕ} (hm : 4 ≤ m) {i j : Col m} (hn : i ≠ j) :
    Adjacent (by omega : 2 ≤ m) i j ↔ (pairSupport i j).card = 2 ^ (m - 2) := by
  classical
  have h₂ : 2 ≤ m := by omega
  obtain ⟨hlo, hhi⟩ := support_between i j
  constructor
  · intro ha
    rcases (edges_cover h₂ hn).mp ha with ho | he
    · have hO := cutSet_sameEdge hn ho
      have hE := cutSet_distinctEdges (edges_disjoint h₂ hn ho)
      rw [hO, Finset.empty_union, Finset.empty_inter, Finset.sdiff_empty] at hlo
      rw [hO, Finset.empty_union] at hhi
      simpa [Finset.Subset.antisymm hlo hhi] using hE
    · have hE := cutSet_sameEdge hn he
      have hO := cutSet_distinctEdges (fun ho => edges_disjoint h₂ hn ho he)
      rw [hE, Finset.union_empty, Finset.inter_empty, Finset.sdiff_empty] at hlo
      rw [hE, Finset.union_empty] at hhi
      simpa [Finset.Subset.antisymm hlo hhi] using hO
  · intro hc
    by_contra ha
    have hnone : ¬ (SameEdge (oddMatching m) i j ∨ SameEdge (evenMatching m) i j) :=
      mt (edges_cover h₂ hn).mpr ha
    let O := cutSet (oddMatching m) i j
    let E := cutSet (evenMatching m) i j
    have hO : O.card = 2 ^ (m - 2) := cutSet_distinctEdges (fun h => hnone (Or.inl h))
    have hE : E.card = 2 ^ (m - 2) := cutSet_distinctEdges (fun h => hnone (Or.inr h))
    have hInt : (O ∩ E).card ≤ 1 := joint_card_le_one h₂ i j
    have hUnion := Finset.card_union_add_card_inter O E
    have hSub := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_union (s := O) (t := E))
    have hBound : ((O ∪ E) \ (O ∩ E)).card ≤ (pairSupport i j).card := Finset.card_le_card hlo
    have hPow : 4 ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ m - 2)
    omega

theorem pairSupport_card_invariant {m : ℕ} (σ : Equiv.Perm (Col m))
    {c : ℂ} (hc : c ≠ 0) (hs : rename σ (F m) = MvPolynomial.C c * F m) (i j : Col m) :
    (pairSupport (σ i) (σ j)).card = (pairSupport i j).card := by
  classical
  have hv (f : Col m → Bool) :
      eval (boolNumber ∘ (f ∘ σ)) (F m) ≠ 0 ↔ eval (boolNumber ∘ f) (F m) ≠ 0 := by
    change eval ((boolNumber ∘ f) ∘ σ) (F m) ≠ 0 ↔ _
    rw [← eval_rename (k := σ), hs, map_mul, eval_C, mul_ne_zero_iff]
    exact and_iff_right hc
  have hmem (f : Col m → Bool) : f ∈ pairSupport (σ i) (σ j) ↔ f ∘ σ ∈ pairSupport i j := by
    simp only [mem_pairSupport, Function.comp_apply]
    exact and_congr_right fun _ => and_congr_right fun _ => (hv f).symm
  refine Finset.card_bij' (fun f _ => f ∘ σ) (fun g _ => g ∘ σ.symm) ?_ ?_ ?_ ?_
  · intro f hf
    exact (hmem _).mp hf
  · intro g hg
    apply (hmem _).mpr
    simpa [Function.comp_def]
  · intro f _
    funext v
    simp
  · intro g _
    funext v
    simp

theorem dihedral_of_scalar_large {m : ℕ} (hm : 4 ≤ m) (σ : Equiv.Perm (Col m))
    {c : ℂ} (hc : c ≠ 0) (hs : rename σ (F m) = MvPolynomial.C c * F m) : Dihedral σ := by
  apply dihedral_of_preserves_adjacency (by omega)
  intro i j ha
  have hn : i ≠ j := adjacent_ne _ ha
  apply (signed_support_recovers_adjacency hm (σ.injective.ne hn)).mpr
  rw [pairSupport_card_invariant σ hc hs]
  exact (signed_support_recovers_adjacency hm hn).mp ha

#print axioms signed_support_recovers_adjacency
#print axioms dihedral_of_scalar_large

end
end D5.S3.Geometry.KozakiKakei
