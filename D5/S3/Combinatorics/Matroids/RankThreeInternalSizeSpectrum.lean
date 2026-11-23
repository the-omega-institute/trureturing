/- GID: D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: The attainable internal extension sizes form a sharp integer interval. -/

import D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset

noncomputable section

namespace D5.S3.Combinatorics.Matroids.RankThreeInternalSizeSpectrum

section Generic
open Set

variable {I B : Type*} [Finite I] [Finite B]

private theorem subfamily_at_size (base : Set B) (n : ℕ)
    (hn : n ≤ Nat.card I * base.ncard) :
    ∃ family : I → Set B, (∀ i, family i ⊆ base) ∧
      ({p : I × B | p.2 ∈ family p.1} : Set (I × B)).ncard = n := by
  let product : Set (I × B) := univ ×ˢ base
  have cap : product.ncard = Nat.card I * base.ncard := by
    rw [show product = univ ×ˢ base from rfl, Set.ncard_prod, Set.ncard_univ]
  have hfin : product.Finite := Set.toFinite _
  have hn' : n ≤ hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card product hfin, cap]
    exact hn
  obtain ⟨selected, hsub, hcard⟩ := Finset.exists_subset_card_eq hn'
  let family (i : I) : Set B := {b | (i, b) ∈ selected}
  refine ⟨family, ?_, ?_⟩
  · intro i b hb
    exact (hfin.mem_toFinset.mp (hsub hb)).2
  · change (selected : Set (I × B)).ncard = n
    simpa using hcard

private theorem exists_largest_family {B : Type*} [Finite B] (valid : Set B → Prop)
    (empty : valid ∅) :
    ∃ maximal : Set B, valid maximal ∧ ∀ s, valid s → s.ncard ≤ maximal.ncard := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let options : Finset (Set B) := Finset.univ.filter valid
  have nonempty : options.Nonempty := ⟨∅, by simp [options, empty]⟩
  obtain ⟨chosen, hchosen, hmax⟩ := Finset.exists_max_image options Set.ncard nonempty
  exact ⟨chosen, (Finset.mem_filter.mp hchosen).2,
    fun s hs => hmax s (by simp [options, hs])⟩


private theorem fibers_card_le (family : I → Set B) {cap : ℕ}
    (bounded : ∀ i, (family i).ncard ≤ cap) :
    ({p : I × B | p.2 ∈ family p.1} : Set (I × B)).ncard ≤ Nat.card I * cap := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let pieces (i : I) : Set (I × B) := {(i, b) | b ∈ family i}
  have split : ({p : I × B | p.2 ∈ family p.1} : Set (I × B)) =
      ⋃ i ∈ (univ : Set I), pieces i := by
    ext ⟨i, b⟩
    simp [pieces]
  have card_piece (i : I) : (pieces i).ncard = (family i).ncard := by
    apply Set.ncard_image_of_injective
    exact Prod.mk_right_injective i
  have pieces_disjoint : (univ : Set I).PairwiseDisjoint pieces := by
    intro a ha b hb ne
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, eq⟩
    exact ne (congrArg Prod.fst eq.symm)
  rw [split, (Set.toFinite (univ : Set I)).ncard_biUnion
    (fun i _ => Set.toFinite (pieces i)) pieces_disjoint]
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite (univ : Set I))]
  have allIndices : (Set.toFinite (univ : Set I)).toFinset = Finset.univ := by
    ext i
    simp
  simp only [allIndices, card_piece, Nat.card_eq_fintype_card]
  calc
    ∑ i : I, (family i).ncard ≤ ∑ _ : I, cap := Finset.sum_le_sum (fun i _ => bounded i)
    _ = _ := by simp [Nat.mul_comm]


end Generic
open Set
open D5.S3.Combinatorics.Matroids.RankThreeInternalTriplePotentials (Row)
open D5.S3.Combinatorics.Matroids.RankThreeOptimalInternalLatin (latinPoint)
open D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition

variable {d r : ℕ}
variable (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
variable (L : Row d → Fin r → Fin r → Fin r)
variable (P : Row d → ZMod 3 → Set (Set (Fin r)))

private def classPoint (i : Row d × ZMod 3) (a : Fin r) : Row d × ZMod (3 * r) :=
  (i.1, (e i.1).symm (i.2, a))

private def observe (p : Row d × ZMod (3 * r)) : Row d × ZMod 3 :=
  (p.1, (e p.1 p.2).1)

private theorem observe_class (i : Row d × ZMod 3) (a : Fin r) :
    observe e (classPoint e i a) = i := by
  simp [observe, classPoint]

private theorem observe_latin (u : Row d × Fin r × Fin r) (i : Fin 3) :
    observe e (latinPoint e L u i) = (u.1, ZMod.finEquiv 3 i) := by
  unfold observe latinPoint
  rw [Equiv.apply_symm_apply]

private theorem latin_blocks_inj :
    Function.Injective (fun u => Set.range (latinPoint e L u)) := by
  intro u v h
  change Set.range (latinPoint e L u) = Set.range (latinPoint e L v) at h
  have slot (i : Fin 3) : latinPoint e L u i = latinPoint e L v i := by
    have mem : latinPoint e L u i ∈ Set.range (latinPoint e L v) :=
      h ▸ ⟨i,rfl⟩
    obtain ⟨j, eq⟩ := mem
    have badges := congrArg (observe e) eq
    rw [observe_latin, observe_latin] at badges
    have ji : j = i := (ZMod.finEquiv 3).injective (congrArg Prod.snd badges)
    subst j
    exact eq.symm
  have row : u.1 = v.1 := congrArg (fun p : Row d × ZMod (3 * r) => p.1) (slot 0)
  have labels (i : Fin 3) :
      (e u.1 (latinPoint e L u i).2).2 = (e v.1 (latinPoint e L v i).2).2 := by
    rw [row, slot i]
  have zero := labels 0
  have one := labels 1
  simp [latinPoint] at zero one
  exact Prod.ext row (Prod.ext zero one)

private def packingEntries : Set ((Row d × ZMod 3) × Set (Fin r)) :=
  {p | p.2 ∈ P p.1.1 p.1.2}

private theorem counting_decomposition [NeZero (3 * r)]
    (valid : ∀ x c, IsPartialSteiner (P x c)) :
    (extendedFamily e L P).ncard = 3 ^ d * r ^ 2 + (packingEntries P).ncard := by
  classical
  let lat := fun u => Set.range (latinPoint e L u)
  let pack (p : (Row d × ZMod 3) × Set (Fin r)) := classPoint e p.1 '' p.2
  have disjoint : Disjoint (Set.range lat) (pack '' packingEntries P) := by
    refine Set.disjoint_left.mpr ?_
    rintro t ⟨u, rfl⟩ ⟨p, _, eq⟩
    have mono (i : Fin 3) : observe e (latinPoint e L u i) = p.1 := by
      have member : latinPoint e L u i ∈ pack p := by
        rw [eq]
        exact ⟨i,rfl⟩
      obtain ⟨a, _, ha⟩ := member
      rw [← ha, observe_class]
    have h : (ZMod.finEquiv 3 0) = (ZMod.finEquiv 3 1) := by
      have h0 := mono 0
      have h1 := mono 1
      rw [observe_latin] at h0 h1
      exact congrArg Prod.snd (h0.trans h1.symm)
    exact (by decide : (0 : Fin 3) ≠ 1) ((ZMod.finEquiv 3).injective h)
  have injective : Set.InjOn pack (packingEntries P) := by
    rintro ⟨i,s⟩ hs ⟨j,t⟩ ht eq
    change classPoint e i '' s = classPoint e j '' t at eq
    have nonempty : s.Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero
      rw [(valid i.1 i.2).1 s hs]
      decide
    obtain ⟨a, ha⟩ := nonempty
    have member : classPoint e i a ∈ classPoint e j '' t := eq ▸ ⟨a,ha,rfl⟩
    obtain ⟨b, hb, hpoint⟩ := member
    have ij : j = i := by
      simpa only [observe_class] using congrArg (observe e) hpoint
    subst j
    have pInj : Function.Injective (classPoint e i) := by
      intro a b h
      exact congrArg Prod.snd ((e i.1).symm.injective (congrArg Prod.snd h))
    have st : s = t := Set.image_injective.mpr pInj eq
    exact Prod.ext rfl st
  have represent : extendedFamily e L P = (Set.range lat) ∪ (pack '' packingEntries P) := by
    ext t
    constructor
    · rintro (h | ⟨x,c,s,hs,eq⟩)
      · exact Or.inl h
      · exact Or.inr ⟨((x,c),s),hs,eq.symm⟩
    · rintro (h | ⟨⟨⟨x,c⟩,s⟩,hs,eq⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x,c,s,hs,eq.symm⟩
  rw [represent, Set.ncard_union_eq disjoint, injective.ncard_image,
    Set.ncard_range_of_injective (latin_blocks_inj e L)]
  simp [Row, Nat.card_eq_fintype_card, Fintype.card_prod, pow_two]


open D5.S3.Combinatorics.Matroids.RankThreeInternalTriplePotentials (LiftedLineFamily)
open D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentialFibers (potentialSpace)
open D5.S3.Combinatorics.Matroids.RankThreeOmissionPotentials (covers IsOmissionPotential)
open D5.S3.Combinatorics.LatinEulerianMultiples (IsLatin)

private theorem largest_packing (r : ℕ) :
    ∃ Q : Set (Set (Fin r)), IsPartialSteiner Q ∧
      ∀ A : Set (Set (Fin r)), IsPartialSteiner A → A.ncard ≤ Q.ncard :=
  exists_largest_family IsPartialSteiner ⟨by simp, by simp⟩

/-- The largest number of triples in a partial Steiner system on `Fin r`. -/
def packingNumber (r : ℕ) : ℕ := (Classical.choose (largest_packing r)).ncard

private theorem subset_packing {A Q : Set (Set (Fin r))}
    (valid : IsPartialSteiner Q) (sub : A ⊆ Q) : IsPartialSteiner A := by
  constructor
  · intro s hs
    exact valid.1 s (sub hs)
  · intro s hs t ht a b hne hsa hsb hta htb
    exact valid.2 s (sub hs) t (sub ht) a b hne hsa hsb hta htb

private theorem potential_reindex {X A B : Type*} [Fintype X]
    (f : A → Fin 3 → X) (g : B → Fin 3 → X) (equiv : A ≃ B)
    (reindex : ∀ a, g (equiv a) = f a) (anchor : X) :
    potentialSpace f anchor = potentialSpace g anchor := by
  ext u
  change IsOmissionPotential f anchor u ↔ IsOmissionPotential g anchor u
  have cover (x y : X) :
      (∃ t a b, f t a = x ∧ f t b = y) ↔ (∃ t a b, g t a = x ∧ g t b = y) := by
    constructor
    · rintro ⟨t,a,b,ha,hb⟩
      exact ⟨equiv t, a, b, by simpa only [reindex] using ha, by simpa only [reindex] using hb⟩
    · rintro ⟨t,a,b,ha,hb⟩
      obtain ⟨t, rfl⟩ := equiv.surjective t
      exact ⟨t, a, b, by simpa only [reindex] using ha, by simpa only [reindex] using hb⟩
  constructor
  · rintro ⟨h0,hs,ht,hp,hl⟩
    refine ⟨h0,hs,ht,fun x y notCov => hp x y (notCov ∘ (cover x y).mp), ?_⟩
    intro t
    obtain ⟨t, rfl⟩ := equiv.surjective t
    simpa only [reindex] using hl t
  · rintro ⟨h0,hs,ht,hp,hl⟩
    refine ⟨h0,hs,ht,fun x y notCov => hp x y (notCov ∘ (cover x y).mpr), ?_⟩
    intro t
    simpa only [reindex] using hl (equiv t)

private theorem latin_exists (r : ℕ) [NeZero r] :
    ∃ L : Fin r → Fin r → Fin r, IsLatin r L := by
  let E := (ZMod.finEquiv r).toEquiv
  let L (a b : Fin r) := E.symm (E a + E b)
  refine ⟨L, ?_, ?_⟩
  · intro a
    exact (E.trans ((Equiv.addLeft (E a)).trans E.symm)).bijective
  · intro b
    exact (E.trans ((Equiv.addRight (E b)).trans E.symm)).bijective

/-- The attainable sizes of pair-unique internal extensions form the whole integer
interval from the Latin minimum to the independent packing maximum. -/
theorem exact_size_spectrum {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (hd : 0 < d)
    (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (mixedUnique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u)
    (N : ℕ) :
    (∃ (U : Type) (internal : U → Fin 3 → Row d × ZMod (3 * r)),
      let combined := Sum.elim mixed internal
      (∀ u i, (internal u i).1 = (internal u 0).1) ∧
      (∀ u, Function.Injective (internal u)) ∧
      (∀ t u x y, x ≠ y → covers (combined t) x y → covers (combined u) x y → t = u) ∧
      Module.finrank (ZMod 3) (potentialSpace combined 0) = d + 1 ∧
      (Set.range (fun u => Set.range (internal u))).ncard = N) ↔
    3 ^ d * r ^ 2 ≤ N ∧ N ≤ 3 ^ d * r ^ 2 + 3 ^ (d + 1) * packingNumber r := by
  classical
  let Q := Classical.choose (largest_packing r)
  have hQ := Classical.choose_spec (largest_packing r)
  have observedClasses : Nat.card (Row d × ZMod 3) = 3 ^ (d + 1) := by
    simp [Row, Nat.card_eq_fintype_card, Fintype.card_prod, pow_succ]
  constructor
  · rintro ⟨U,internal,same,inj,pair,dim,count⟩
    obtain ⟨L,P,_,hP,split⟩ :=
      forward_decomposition e he hd mixed internal family crosses same inj pair dim
    have hcount := counting_decomposition e L P hP
    rw [split, hcount] at count
    have maxCard : (packingEntries P).ncard ≤ 3 ^ (d + 1) * packingNumber r := by
      rw [← observedClasses]
      exact fibers_card_le (fun i : Row d × ZMod 3 => P i.1 i.2)
        (fun i => hQ.2 _ (hP i.1 i.2))
    exact ⟨by omega, by omega⟩
  · rintro ⟨lo, hi⟩
    have : NeZero r := ⟨fun zero => NeZero.ne (3 * r) (by simp [zero])⟩
    obtain ⟨K,hK⟩ := latin_exists r
    let L : Row d → Fin r → Fin r → Fin r := fun _ => K
    let n := N - 3 ^ d * r ^ 2
    have hn : n ≤ Nat.card (Row d × ZMod 3) * Q.ncard := by
      rw [observedClasses]
      change n ≤ 3 ^ (d + 1) * packingNumber r
      omega
    obtain ⟨A,hA,hCard⟩ := subfamily_at_size Q n hn
    let P (x : Row d) (c : ZMod 3) := A (x,c)
    have valid (x : Row d) (c : ZMod 3) : IsPartialSteiner (P x c) :=
      subset_packing hQ.1 (hA (x,c))
    obtain ⟨M, _, mono, unordered, monoData, inj, pair, dim⟩ :=
      realize_decomposition e he hd L (fun _ => hK) P valid mixed family crosses mixedUnique
    let Cell := Row d × Fin r × Fin r
    let internal := Sum.elim (latinPoint e L) mono
    let combined := Sum.elim mixed internal
    let original := Sum.elim (Sum.elim mixed (latinPoint e L)) mono
    let eqv := Equiv.sumAssoc T Cell M
    have aligned (t : (T ⊕ Cell) ⊕ M) : combined (eqv t) = original t := by
      rcases t with (t | t) | t <;> rfl
    refine ⟨Cell ⊕ M, internal, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (u | v) i
      · rfl
      · obtain ⟨x,c,s,hs,hRange⟩ := monoData v
        have sameRow (j : Fin 3) : (mono v j).1 = x := by
          have member : mono v j ∈ (fun a => (x, (e x).symm (c,a))) '' s := by
            rw [← hRange]
            exact ⟨j,rfl⟩
          obtain ⟨a,ha,hpoint⟩ := member
          exact (congrArg Prod.fst hpoint).symm
        exact (sameRow i).trans (sameRow 0).symm
    · rintro (u | v)
      · exact inj (Sum.inl (Sum.inr u))
      · exact inj (Sum.inr v)
    · intro t u x y ne ht hu
      obtain ⟨t,rfl⟩ := eqv.surjective t
      obtain ⟨u,rfl⟩ := eqv.surjective u
      change covers (combined (eqv t)) x y at ht
      change covers (combined (eqv u)) x y at hu
      rw [aligned] at ht hu
      exact congrArg eqv (pair t u x y ne ht hu)
    · have hspace := potential_reindex original combined eqv aligned 0
      rw [← hspace]
      exact dim
    · rw [unordered, counting_decomposition e L P valid]
      change 3 ^ d * r ^ 2 + ({p : (Row d × ZMod 3) × Set (Fin r) | p.2 ∈ A p.1}).ncard = N
      rw [hCard]
      omega


end D5.S3.Combinatorics.Matroids.RankThreeInternalSizeSpectrum
