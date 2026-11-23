/- GID: D5/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeInternalSizeSpectrum
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Internal extension sizes form an interval, and saturated sizes with six labels form a step-two progression. -/

import D5.S3.Combinatorics.Matroids.RankThreeInternalSteinerDecomposition
import D5.S3.Combinatorics.Matroids.RankThreeMinimumInternalAdditions
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset

/-! # Sizes and saturation of ternary internal extensions -/

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


private theorem fibers_card_eq [Fintype I] (family : I → Set B) :
    ({p : I × B | p.2 ∈ family p.1} : Set (I × B)).ncard = ∑ i : I, (family i).ncard := by
  classical
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
  simp only [allIndices, card_piece]

private theorem fibers_card_le (family : I → Set B) {cap : ℕ}
    (bounded : ∀ i, (family i).ncard ≤ cap) :
    ({p : I × B | p.2 ∈ family p.1} : Set (I × B)).ncard ≤ Nat.card I * cap := by
  classical
  let : Fintype I := Fintype.ofFinite I
  rw [fibers_card_eq, Nat.card_eq_fintype_card]
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

/-- An unordered family obtained by a pair-unique same-row extension with the extra dimension. -/
def IsInternalExtension {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (G : Set (Set (Row d × ZMod (3 * r)))) : Prop :=
  ∃ (U : Type) (internal : U → Fin 3 → Row d × ZMod (3 * r)),
    let combined := Sum.elim mixed internal
    (∀ u i, (internal u i).1 = (internal u 0).1) ∧
    (∀ u, Function.Injective (internal u)) ∧
    (∀ t u x y, x ≠ y → covers (combined t) x y → covers (combined u) x y → t = u) ∧
    Module.finrank (ZMod 3) (potentialSpace combined 0) = d + 1 ∧
    Set.range (fun u => Set.range (internal u)) = G

/-- A dimension-preserving internal extension with no proper compatible enlargement. -/
def IsSaturatedInternalExtension {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (G : Set (Set (Row d × ZMod (3 * r)))) : Prop :=
  IsInternalExtension mixed G ∧
    ∀ H, IsInternalExtension mixed H → G ⊆ H → H = G

private theorem realize_internal_extension {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (mixedUnique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u)
    (L : Row d → Fin r → Fin r → Fin r) (hL : ∀ x, IsLatin r (L x))
    (P : Row d → ZMod 3 → Set (Set (Fin r))) (valid : ∀ x c, IsPartialSteiner (P x c)) :
    IsInternalExtension mixed (extendedFamily e L P) := by
  obtain ⟨M, _, mono, unordered, monoData, inj, pair, dim⟩ :=
    realize_decomposition e he hd L hL P valid mixed family crosses mixedUnique
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
  · exact unordered

/-- The attainable sizes of pair-unique internal extensions form the whole integer
interval from the Latin minimum to the independent packing maximum. -/
theorem exact_size_spectrum {d r : ℕ} [NeZero (3 * r)] {T : Type*}
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
  obtain ⟨labels, hlabels⟩ := RankThreeMinimumInternalAdditions.residue_indexing r
  let e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r) := fun _ => labels
  have he (x : Row d) (a : ZMod (3 * r)) :
      (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a := hlabels a
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
    obtain ⟨U, internal, same, inj, pair, dim, unordered⟩ :=
      realize_internal_extension e he hd mixed family crosses mixedUnique L (fun _ => hK) P valid
    refine ⟨U, internal, same, inj, pair, dim, ?_⟩
    · rw [unordered, counting_decomposition e L P valid]
      change 3 ^ d * r ^ 2 + ({p : (Row d × ZMod 3) × Set (Fin r) | p.2 ∈ A p.1}).ncard = N
      rw [hCard]
      omega

private theorem packing_ne_cell (L : Row d → Fin r → Fin r → Fin r)
    (u : Row d × Fin r × Fin r) (x : Row d) (c : ZMod 3) (s : Set (Fin r)) :
    Set.range (latinPoint e L u) ≠ (fun a => (x, (e x).symm (c, a))) '' s := by
  intro eq
  have same (i : Fin 3) : observe e (latinPoint e L u i) = (x,c) := by
    have member : latinPoint e L u i ∈ (fun a => (x,(e x).symm (c,a))) '' s :=
      eq ▸ ⟨i,rfl⟩
    obtain ⟨a,ha,hp⟩ := member
    rw [← hp]
    exact observe_class e (x,c) a
  have h := (same 0).trans (same 1).symm
  rw [observe_latin, observe_latin] at h
  exact (by decide : (0 : Fin 3) ≠ 1) ((ZMod.finEquiv 3).injective (congrArg Prod.snd h))

private theorem equal_cells_have_equal_slots (L K : Row d → Fin r → Fin r → Fin r)
    (u v : Row d × Fin r × Fin r)
    (eq : Set.range (latinPoint e L u) = Set.range (latinPoint e K v)) :
    latinPoint e L u = latinPoint e K v := by
  funext i
  have member : latinPoint e L u i ∈ Set.range (latinPoint e K v) := eq ▸ ⟨i,rfl⟩
  obtain ⟨j,hp⟩ := member
  have observed := congrArg (observe e) hp
  rw [observe_latin, observe_latin] at observed
  have ji : j = i := (ZMod.finEquiv 3).injective (congrArg Prod.snd observed)
  subst j
  exact hp.symm

private theorem subset_data
    (L K : Row d → Fin r → Fin r → Fin r)
    (P Q : Row d → ZMod 3 → Set (Set (Fin r)))
    (hP : ∀ x c, IsPartialSteiner (P x c))
    (h : extendedFamily e L P ⊆ extendedFamily e K Q) :
    L = K ∧ ∀ x c, P x c ⊆ Q x c := by
  constructor
  · funext x a b
    let u : Row d × Fin r × Fin r := (x,a,b)
    have member : Set.range (latinPoint e L u) ∈ extendedFamily e K Q :=
      h (Or.inl ⟨u,rfl⟩)
    rcases member with ⟨⟨y,c,f⟩,eq⟩ | ⟨y,i,s,hs,eq⟩
    · have slots := equal_cells_have_equal_slots e L K u (y,c,f) eq.symm
      have row : x = y := congrArg (fun p : Fin 3 → Row d × ZMod (3*r) => (p 0).1) slots
      subst y
      have labels (i : Fin 3) : (e x (latinPoint e L u i).2).2 =
          (e x (latinPoint e K (x,c,f) i).2).2 := by rw [slots]
      have left : a = c := by simpa [latinPoint,u] using labels 0
      have right : b = f := by simpa [latinPoint,u] using labels 1
      subst c
      subst f
      simpa [latinPoint,u] using labels 2
    · exact (packing_ne_cell e L u y i s eq).elim
  · intro x c s hs
    let point (a : Fin r) := (x, (e x).symm (c,a))
    have member : point '' s ∈ extendedFamily e K Q := h (Or.inr ⟨x,c,s,hs,rfl⟩)
    rcases member with ⟨u,eq⟩ | ⟨y,b,t,ht,eq⟩
    · exact (packing_ne_cell e K u x c s eq).elim
    · have nonempty : s.Nonempty := by
        apply Set.nonempty_of_ncard_ne_zero
        rw [(hP x c).1 s hs]
        decide
      obtain ⟨a,ha⟩ := nonempty
      have hpoint : point a ∈ (fun u => (y, (e y).symm (b,u))) '' t :=
        eq ▸ ⟨a,ha,rfl⟩
      obtain ⟨v,hv,hv_eq⟩ := hpoint
      have observed := congrArg (observe e) hv_eq
      change observe e (y,(e y).symm (b,v)) = observe e (x,(e x).symm (c,a)) at observed
      change observe e (classPoint e (y,b) v) = observe e (classPoint e (x,c) a) at observed
      rw [observe_class, observe_class] at observed
      have row : y = x := congrArg Prod.fst observed
      have res : b = c := congrArg Prod.snd observed
      subst y
      subst b
      have pinj : Function.Injective point := by
        intro v w hvw
        exact congrArg Prod.snd ((e x).symm.injective (congrArg Prod.snd hvw))
      have st : s = t := Set.image_injective.mpr pinj eq
      exact st.symm ▸ ht



private theorem data_subset
    (L : Row d → Fin r → Fin r → Fin r)
    (P Q : Row d → ZMod 3 → Set (Set (Fin r)))
    (h : ∀ x c, P x c ⊆ Q x c) :
    extendedFamily e L P ⊆ extendedFamily e L Q := by
  rintro s (hs | ⟨x,c,t,ht,eq⟩)
  · exact Or.inl hs
  · exact Or.inr ⟨x,c,t,h x c ht,eq⟩

private theorem represented_maximal_iff
    (L : Row d → Fin r → Fin r → Fin r) (hL : ∀ x, IsLatin r (L x))
    (P : Row d → ZMod 3 → Set (Set (Fin r))) (hP : ∀ x c, IsPartialSteiner (P x c)) :
    (∀ K Q, (∀ x, IsLatin r (K x)) → (∀ x c, IsPartialSteiner (Q x c)) →
      extendedFamily e L P ⊆ extendedFamily e K Q →
      extendedFamily e K Q = extendedFamily e L P) ↔
    (∀ x c S, IsPartialSteiner S → P x c ⊆ S → S = P x c) := by
  classical
  constructor
  · intro noExtension x c S valid contains
    let U : (Row d × ZMod 3) → Set (Set (Fin r)) :=
      Function.update (fun i => P i.1 i.2) (x,c) S
    let Q (y : Row d) (b : ZMod 3) := U (y,b)
    have data (i : Row d × ZMod 3) : IsPartialSteiner (U i) ∧ P i.1 i.2 ⊆ U i := by
      by_cases same : i = (x,c)
      · subst i
        simpa [U] using And.intro valid contains
      · simpa [U, Function.update_of_ne same] using
          (And.intro (hP i.1 i.2) (Subset.rfl : P i.1 i.2 ⊆ P i.1 i.2))
    have hQ (y : Row d) (b : ZMod 3) : IsPartialSteiner (Q y b) := (data (y,b)).1
    have hat (y : Row d) (b : ZMod 3) : P y b ⊆ Q y b := (data (y,b)).2
    have target := noExtension L Q hL hQ (data_subset e L P Q hat)
    have backwards := (subset_data e L L Q P hQ target.subset).2
    apply Set.Subset.antisymm _ contains
    simpa [Q,U] using backwards x c
  · intro localMax K Q _ hQ sub
    obtain ⟨squares,packs⟩ := subset_data e L K P Q hP sub
    subst K
    have eq : Q = P := funext fun x => funext fun c => localMax x c (Q x c) (hQ x c) (packs x c)
    rw [eq]

private theorem internal_extension_iff {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (mixedUnique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u)
    (G : Set (Set (Row d × ZMod (3 * r)))) :
    IsInternalExtension mixed G ↔
      ∃ L P, (∀ x, IsLatin r (L x)) ∧ (∀ x c, IsPartialSteiner (P x c)) ∧
        extendedFamily e L P = G := by
  constructor
  · rintro ⟨U,internal,same,inj,pair,dim,rfl⟩
    obtain ⟨L,P,latin,valid,split⟩ :=
      forward_decomposition e he hd mixed internal family crosses same inj pair dim
    exact ⟨L,P,latin,valid,split.symm⟩
  · rintro ⟨L,P,hL,valid,rfl⟩
    exact realize_internal_extension e he hd mixed family crosses mixedUnique L hL P valid


/-- If a compatible enlargement exists, any one of its new triples can be added first. -/
theorem internal_extension_insert {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (mixedUnique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u)
    (G H : Set (Set (Row d × ZMod (3 * r))))
    (validG : IsInternalExtension mixed G) (validH : IsInternalExtension mixed H)
    (sub : G ⊆ H) {block : Set (Row d × ZMod (3 * r))} (member : block ∈ H) :
    IsInternalExtension mixed (insert block G) := by
  classical
  by_cases old : block ∈ G
  · simpa [Set.insert_eq_of_mem old] using validG
  obtain ⟨labels,hlabels⟩ := RankThreeMinimumInternalAdditions.residue_indexing r
  let e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r) := fun _ => labels
  have he (x : Row d) (a : ZMod (3 * r)) :
      (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a := hlabels a
  let bridge := internal_extension_iff e he hd mixed family crosses mixedUnique
  obtain ⟨L,P,hL,hP,rfl⟩ := (bridge G).mp validG
  obtain ⟨K,Q,_,hQ,rfl⟩ := (bridge H).mp validH
  obtain ⟨rfl,inc⟩ := subset_data e L K P Q hP sub
  rcases member with latin | ⟨x,c,s,hs,rfl⟩
  · exact (old (Or.inl latin)).elim
  · let R (y : Row d) (b : ZMod 3) :=
      Function.update (fun i : Row d × ZMod 3 => P i.1 i.2) (x,c) (insert s (P x c)) (y,b)
    have valid (y : Row d) (b : ZMod 3) : IsPartialSteiner (R y b) := by
      by_cases eq : (y,b) = (x,c)
      · cases Prod.mk.inj eq with
        | intro hx hb =>
          subst y
          subst b
          simpa [R] using subset_packing (hQ x c) (Set.insert_subset hs (inc x c))
      · simpa [R, Function.update_of_ne eq] using hP y b
    apply (bridge _).mpr
    refine ⟨L,R,hL,valid,?_⟩
    ext t
    constructor
    · rintro (latin | ⟨y,b,u,hu,rfl⟩)
      · exact Or.inr (Or.inl latin)
      · by_cases eq : (y,b) = (x,c)
        · cases Prod.mk.inj eq with
          | intro hx hb =>
            subst y
            subst b
            have mem : u ∈ insert s (P x c) := by simpa [R] using hu
            rcases mem with rfl | mem
            · exact Or.inl rfl
            · exact Or.inr (Or.inr ⟨x,c,u,mem,rfl⟩)
        · have mem : u ∈ P y b := by simpa [R, Function.update_of_ne eq] using hu
          exact Or.inr (Or.inr ⟨y,b,u,mem,rfl⟩)
    · rintro (rfl | latin | ⟨y,b,u,hu,rfl⟩)
      · exact Or.inr ⟨x,c,s,by simp [R],rfl⟩
      · exact Or.inl latin
      · refine Or.inr ⟨y,b,u,?_,rfl⟩
        by_cases eq : (y,b) = (x,c)
        · cases Prod.mk.inj eq with
          | intro hx hb =>
            subst y
            subst b
            simp [R, hu]
        · simpa [R, Function.update_of_ne eq] using hu

namespace SixLabels

private abbrev Block := Finset (Fin 6)
private abbrev Packing := Finset Block

private def triples : Packing := (Finset.univ : Block).powersetCard 3

private def pairUnique (F : Packing) : Prop :=
  ∀ s ∈ F, ∀ t ∈ F, s ≠ t → (s ∩ t).card ≤ 1

private instance (F : Packing) : Decidable (pairUnique F) := by
  unfold pairUnique
  infer_instance

private def maximal (F : Packing) : Prop :=
  pairUnique F ∧ ∀ t ∈ triples, t ∉ F → ¬ pairUnique (insert t F)

private instance (F : Packing) : Decidable (maximal F) := by
  unfold maximal
  infer_instance

private def pool : List Block :=
  [{0,1,2}, {0,1,3}, {0,1,4}, {0,1,5}, {0,2,3}, {0,2,4}, {0,2,5},
    {0,3,4}, {0,3,5}, {0,4,5}, {1,2,3}, {1,2,4}, {1,2,5}, {1,3,4},
    {1,3,5}, {1,4,5}, {2,3,4}, {2,3,5}, {2,4,5}, {3,4,5}]

private theorem pool_complete : ∀ t ∈ triples, t ∈ pool := by decide +kernel

private def verify : List Block → Packing → Bool
  | [], picked => decide (maximal picked → picked.card = 2 ∨ picked.card = 4)
  | t :: rest, picked =>
      verify rest picked &&
        (if pairUnique (insert t picked) then verify rest (insert t picked) else true)

private theorem pairUnique_of_subset {A B : Packing} (inc : A ⊆ B)
    (hB : pairUnique B) : pairUnique A :=
  fun s hs t ht ne => hB s (inc hs) t (inc ht) ne

private theorem verify_sound (F : Packing) (valid : maximal F) :
    ∀ (rest : List Block) (picked : Packing), picked ⊆ F →
      (∀ t ∈ F, t ∉ picked → t ∈ rest) →
      verify rest picked = true → F.card = 2 ∨ F.card = 4 := by
  intro rest
  induction rest with
  | nil =>
    intro picked sub missing checked
    have eq : picked = F := Finset.Subset.antisymm sub (by
      intro t ht
      by_contra absent
      exact List.not_mem_nil (missing t ht absent))
    subst picked
    exact (of_decide_eq_true checked) valid
  | cons t rest ih =>
    intro picked sub missing checked
    simp only [verify, Bool.and_eq_true] at checked
    by_cases member : t ∈ F
    · have addSub : insert t picked ⊆ F := Finset.insert_subset member sub
      have addValid := pairUnique_of_subset addSub valid.1
      apply ih (insert t picked) addSub _ (by simpa [addValid] using checked.2)
      intro x hx absent
      have notPicked : x ∉ picked := fun h => absent (Finset.mem_insert_of_mem h)
      have different : x ≠ t := fun h => absent (h ▸ Finset.mem_insert_self t picked)
      exact (List.mem_cons.mp (missing x hx notPicked)).resolve_left different
    · apply ih picked sub _ checked.1
      intro x hx absent
      exact (List.mem_cons.mp (missing x hx absent)).resolve_left (fun eq => member (eq ▸ hx))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem verify_pool : verify pool ∅ = true := by decide +kernel

private theorem maximal_size (F : Packing) (sub : F ⊆ triples) (h : maximal F) :
    F.card = 2 ∨ F.card = 4 :=
  verify_sound F h pool ∅ (Finset.empty_subset _) (fun t ht _ => pool_complete t (sub ht)) verify_pool

private theorem witnessTwo : maximal ({{0,1,2}, {3,4,5}} : Packing) := by decide +kernel

private theorem witnessFour :
    maximal ({{0,1,2}, {0,3,4}, {1,3,5}, {2,4,5}} : Packing) := by decide +kernel

private def packSets (F : Packing) : Set (Set (Fin 6)) :=
  (fun s : Block => (s : Set (Fin 6))) '' (F : Set Block)

private theorem packSets_card (F : Packing) : (packSets F).ncard = F.card := by
  rw [packSets, Set.ncard_image_of_injective _ Finset.coe_injective, Set.ncard_coe_finset]

private theorem packSets_partial (F : Packing) :
    IsPartialSteiner (packSets F) ↔ F ⊆ triples ∧ pairUnique F := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro s hs
      have hc := h.1 (s : Set (Fin 6)) ⟨s,hs,rfl⟩
      simpa [triples] using hc
    · intro s hs t ht ne
      apply Finset.card_le_one.mpr
      intro a ha b hb
      by_contra diff
      have obs := h.2 (s : Set (Fin 6)) ⟨s,hs,rfl⟩ (t : Set (Fin 6)) ⟨t,ht,rfl⟩
        a b diff (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp hb).1
        (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
      exact ne (Finset.coe_injective obs)
  · rintro ⟨sub, valid⟩
    constructor
    · rintro _ ⟨s,hs,rfl⟩
      have hc := (Finset.mem_powersetCard.mp (sub hs)).2
      simpa using hc
    · rintro _ ⟨s,hs,rfl⟩ _ ⟨t,ht,rfl⟩ a b ne ha hb hta htb
      by_contra diff
      have diff' : s ≠ t := fun eq => diff (by rw [eq])
      exact ne (Finset.card_le_one.mp (valid s hs t ht diff') a
        (Finset.mem_inter.mpr ⟨ha,hta⟩) b (Finset.mem_inter.mpr ⟨hb,htb⟩))

private theorem packSets_sub {F G : Packing} :
    packSets F ⊆ packSets G ↔ F ⊆ G := by
  constructor
  · intro h s hs
    obtain ⟨t, ht, eq⟩ := h (show (s : Set (Fin 6)) ∈ packSets F from ⟨s,hs,rfl⟩)
    exact Finset.coe_injective eq ▸ ht
  · exact Set.image_mono

private theorem packSets_surj (S : Set (Set (Fin 6))) : ∃ F, packSets F = S := by
  classical
  let sf := (Set.toFinite S).toFinset
  refine ⟨sf.image (fun s => (Set.toFinite s).toFinset), ?_⟩
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    simpa using (Set.Finite.mem_toFinset (Set.toFinite S)).mp hs
  · intro hx
    refine ⟨(Set.toFinite x).toFinset, Finset.mem_image.mpr ⟨x,?_,rfl⟩, by simp⟩
    exact (Set.Finite.mem_toFinset (Set.toFinite S)).mpr hx

private theorem packSets_maximal (F : Packing) (h : maximal F) :
    ∀ S, IsPartialSteiner S → packSets F ⊆ S → S = packSets F := by
  intro S hS inc
  obtain ⟨G,rfl⟩ := packSets_surj S
  have fg := packSets_sub.mp inc
  have valid := (packSets_partial G).mp hS
  congr 1
  exact Finset.Subset.antisymm (by
    intro t ht
    by_contra miss
    exact h.2 t (valid.1 ht) miss
      (pairUnique_of_subset (Finset.insert_subset ht fg) valid.2)) fg

private theorem maximal_packSets_size (S : Set (Set (Fin 6))) (valid : IsPartialSteiner S)
    (noExtension : ∀ U, IsPartialSteiner U → S ⊆ U → U = S) :
    S.ncard = 2 ∨ S.ncard = 4 := by
  obtain ⟨F,rfl⟩ := packSets_surj S
  have hv := (packSets_partial F).mp valid
  rw [packSets_card]
  refine maximal_size F hv.1 ⟨hv.2, ?_⟩
  intro t ht notF addValid
  have addSub := Finset.insert_subset ht hv.1
  have addPartial := (packSets_partial _).mpr ⟨addSub, addValid⟩
  have eq := noExtension _ addPartial (packSets_sub.mpr (Finset.subset_insert _ _))
  exact notF (packSets_sub.mp eq.subset (Finset.mem_insert_self _ _))

private def twoBlocks : Packing := {{0,1,2},{3,4,5}}
private def fourBlocks : Packing := {{0,1,2},{0,3,4},{1,3,5},{2,4,5}}

private theorem two_valid : IsPartialSteiner (packSets twoBlocks) :=
  (packSets_partial _).mpr ⟨by decide +kernel,witnessTwo.1⟩
private theorem four_valid : IsPartialSteiner (packSets fourBlocks) :=
  (packSets_partial _).mpr ⟨by decide +kernel,witnessFour.1⟩

end SixLabels


/-- Saturation is equivalent to inclusion maximality in every residue class. -/
theorem saturated_internal_extension_iff {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r))
    (he : ∀ x a, (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a)
    (hd : 0 < d) (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (mixedUnique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u)
    (G : Set (Set (Row d × ZMod (3 * r)))) :
    IsSaturatedInternalExtension mixed G ↔
      ∃ L P, (∀ x, IsLatin r (L x)) ∧ (∀ x c, IsPartialSteiner (P x c)) ∧
        (∀ x c S, IsPartialSteiner S → P x c ⊆ S → S = P x c) ∧
        extendedFamily e L P = G := by
  let bridge := internal_extension_iff e he hd mixed family crosses mixedUnique
  constructor
  · rintro ⟨valid, maximal⟩
    obtain ⟨L,P,hL,hP,rfl⟩ := (bridge G).mp valid
    refine ⟨L,P,hL,hP,(represented_maximal_iff e L hL P hP).mp ?_,rfl⟩
    intro K Q hK hQ sub
    exact maximal _ ((bridge _).mpr ⟨K,Q,hK,hQ,rfl⟩) sub
  · rintro ⟨L,P,hL,hP,localMax,rfl⟩
    refine ⟨(bridge _).mpr ⟨L,P,hL,hP,rfl⟩, ?_⟩
    intro H valid contains
    obtain ⟨K,Q,hK,hQ,rfl⟩ := (bridge H).mp valid
    exact (represented_maximal_iff e L hL P hP).mpr localMax K Q hK hQ contains

private theorem packingEntries_count {d : ℕ} (P : Row d → ZMod 3 → Set (Set (Fin 6)))
    (selected : Finset (Row d × ZMod 3))
    (h : ∀ i : Row d × ZMod 3, (P i.1 i.2).ncard = 2 + if i ∈ selected then 2 else 0) :
    (packingEntries P).ncard = 2 * 3 ^ (d + 1) + 2 * selected.card := by
  classical
  rw [packingEntries, fibers_card_eq (fun i : Row d × ZMod 3 => P i.1 i.2)]
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter]
  have classes : Fintype.card (Row d × ZMod 3) = 3 ^ (d + 1) := by
    simp [Row, Fintype.card_prod, pow_succ]
  have filter : Finset.univ.filter (fun i => i ∈ selected) = selected := by ext; simp
  simp [classes, filter, Nat.mul_comm]

/-- With six labels per residue class, the saturated sizes form a progression of step two. -/
theorem saturated_six_size_spectrum {d : ℕ} {T : Type*}
    (hd : 0 < d)
    (mixed : T → Fin 3 → Row d × ZMod (3 * 6))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (mixedUnique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u)
    (N : ℕ) :
    (∃ G, IsSaturatedInternalExtension mixed G ∧ G.ncard = N) ↔
      ∃ k ≤ 3 ^ (d + 1), N = 3 ^ d * 6 ^ 2 + 2 * 3 ^ (d + 1) + 2 * k := by
  classical
  obtain ⟨labels, hlabels⟩ := RankThreeMinimumInternalAdditions.residue_indexing 6
  let e : Row d → (ZMod (3 * 6) ≃ ZMod 3 × Fin 6) := fun _ => labels
  have he (x : Row d) (a : ZMod (3 * 6)) :
      (e x a).1 = ZMod.castHom (dvd_mul_right 3 6) (ZMod 3) a := hlabels a
  let bridge := saturated_internal_extension_iff e he hd mixed family crosses mixedUnique
  have classes : Fintype.card (Row d × ZMod 3) = 3 ^ (d + 1) := by
    simp [Row, Fintype.card_prod, pow_succ]
  constructor
  · rintro ⟨G,hG,count⟩
    obtain ⟨L,P,_,hP,localMax,rfl⟩ := (bridge G).mp hG
    let selected : Finset (Row d × ZMod 3) :=
      Finset.univ.filter (fun i => (P i.1 i.2).ncard = 4)
    have card_at (i : Row d × ZMod 3) :
        (P i.1 i.2).ncard = 2 + if i ∈ selected then 2 else 0 := by
      rcases SixLabels.maximal_packSets_size _ (hP i.1 i.2) (localMax i.1 i.2) with h | h
      · simp [selected, h]
      · simp [selected, h]
    refine ⟨selected.card, ?_, ?_⟩
    · rw [← classes]
      exact Finset.card_le_univ selected
    · rw [← count, counting_decomposition e L P hP, packingEntries_count P selected card_at]
      omega
  · rintro ⟨k, bound, rfl⟩
    have bound' : k ≤ (Finset.univ : Finset (Row d × ZMod 3)).card := by simpa [classes] using bound
    obtain ⟨selected, _, chosen⟩ := Finset.exists_subset_card_eq bound'
    obtain ⟨square, latin⟩ := latin_exists 6
    let L : Row d → Fin 6 → Fin 6 → Fin 6 := fun _ => square
    let P (x : Row d) (c : ZMod 3) :=
      SixLabels.packSets (if (x,c) ∈ selected then SixLabels.fourBlocks else SixLabels.twoBlocks)
    have hP (x : Row d) (c : ZMod 3) : IsPartialSteiner (P x c) := by
      by_cases h : (x,c) ∈ selected
      · simpa [P, h] using SixLabels.four_valid
      · simpa [P, h] using SixLabels.two_valid
    have localMax (x : Row d) (c : ZMod 3) (S : Set (Set (Fin 6)))
        (valid : IsPartialSteiner S) (sub : P x c ⊆ S) : S = P x c := by
      by_cases h : (x,c) ∈ selected
      · simp [P, h] at sub ⊢
        exact SixLabels.packSets_maximal _ SixLabels.witnessFour S valid sub
      · simp [P, h] at sub ⊢
        exact SixLabels.packSets_maximal _ SixLabels.witnessTwo S valid sub
    have card_at (i : Row d × ZMod 3) :
        (P i.1 i.2).ncard = 2 + if i ∈ selected then 2 else 0 := by
      by_cases h : i ∈ selected
      · simp [P, h, SixLabels.packSets_card]
        decide
      · simp [P, h, SixLabels.packSets_card]
        decide
    refine ⟨extendedFamily e L P, (bridge _).mpr ⟨L,P,fun _ => latin,hP,localMax,rfl⟩, ?_⟩
    rw [counting_decomposition e L P hP, packingEntries_count P selected card_at, chosen]
    omega


end D5.S3.Combinatorics.Matroids.RankThreeInternalSizeSpectrum
