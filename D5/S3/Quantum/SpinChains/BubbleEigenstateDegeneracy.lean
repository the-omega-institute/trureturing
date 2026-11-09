/- GID: D5/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/BubbleEigenstateDegeneracy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Closed counting formula for labelled hard-core bubble placements on a cycle. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraRunCompositions

/-!
The bubble-state count of Mukherjee, Banerjee, Sengupta and Sen, arXiv:2106.14897v3,
is the number of labelled placements of three-site units separated by two down spins.
Here the sites are `Fin L`, and both clockwise distances between distinct centres are at least
five. Translations are counted separately. The source's identification with Hamiltonian
eigenstates is outside this counting statement.

Marking a centre converts the cyclic gaps to positive lengths summing to `L - 4 * n`.
The resulting bijection, the label count, and the empty placement give the closed form for
`L ≥ 5`. In particular, the natural-number division in its placement coefficient is exact.
-/

@[expose] public section

namespace D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy

open scoped BigOperators
open D5.S3.Combinatorics.Geometry.MiuraRunCompositions

/-- Clockwise distances between distinct centres are at least five sites.
The quantification over ordered pairs imposes the condition in both directions. -/
def Admissible (L : ℕ) (B : Finset (Fin L)) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a ≠ b →
    5 ≤ if a.val < b.val then b.val - a.val else L + b.val - a.val

/-- Count centre sets and their subsets of centres labelled X; all other centres are Y. -/
noncomputable def bubbleCount (L : ℕ) (E : ℤ) : ℕ := by
  classical
  exact ∑ B ∈ (Finset.univ : Finset (Finset (Fin L))).filter (Admissible L),
    (B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E)).card

/-- The closed form counts placements without identifying translations. -/
def claim : Prop :=
  ∀ L : ℕ, 5 ≤ L → ∀ E : ℤ,
    (bubbleCount L E : ℤ) = (if E = 0 then 1 else 0) +
      ∑ n ∈ Finset.Icc 1 (L / 5),
        ((L * (L - 4 * n - 1).choose (n - 1) / n : ℕ) : ℤ) *
          (if ((n : ℤ) + E) % 2 = 0 ∧ |E| ≤ (n : ℤ) then
            (n.choose (((n : ℤ) + E) / 2).toNat : ℤ) else 0)

private noncomputable def placements (L n : ℕ) : Finset (Finset (Fin L)) := by
  classical
  exact Finset.univ.filter (fun B => Admissible L B ∧ B.card = n)

private lemma packing_bound (L : ℕ) (hL : 5 ≤ L) (B : Finset (Fin L))
    (hB : Admissible L B) : 5 * B.card ≤ L := by
  classical
  let f : B × Fin 5 → Fin L := fun p =>
    ⟨if p.1.val.val + p.2.val < L then p.1.val.val + p.2.val
      else p.1.val.val + p.2.val - L, by
      have ha := p.1.val.isLt
      have hi := p.2.isLt
      split_ifs <;> omega⟩
  have hf : Function.Injective f := by
    rintro ⟨a, i⟩ ⟨b, j⟩ he
    have he := congrArg Fin.val he
    change (if a.val.val + i.val < L then a.val.val + i.val
      else a.val.val + i.val - L) =
      (if b.val.val + j.val < L then b.val.val + j.val
      else b.val.val + j.val - L) at he
    have ha := a.val.isLt
    have hb := b.val.isLt
    have hi := i.isLt
    have hj := j.isLt
    have hab : a = b := by
      by_contra hne
      have hab : a.val ≠ b.val := fun h => hne (Subtype.ext h)
      have hdir := hB a.val a.property b.val b.property hab
      have hrev := hB b.val b.property a.val a.property hab.symm
      split_ifs at he hdir hrev <;> omega
    subst b
    have hij : i = j := by
      apply Fin.ext
      split_ifs at he <;> omega
    exact Prod.ext rfl hij
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Nat.mul_comm] using hc

private def gapPrefix {n : ℕ} (f : Fin n → ℕ) (i : ℕ) : ℕ :=
  ∑ j : Fin n with j.val < i, (f j + 4)

private lemma gap_prefix_step {n : ℕ} (f : Fin n → ℕ) (i : Fin n) :
    gapPrefix f (i.val + 1) = gapPrefix f i.val + f i + 4 := by
  simpa only [gapPrefix, ← Nat.le_iff_lt_add_one, ← Fin.le_def, ← Fin.lt_def,
    Finset.filter_ge_eq_Iic, Finset.filter_gt_eq_Iio, Nat.add_assoc] using
    (Finset.sum_Iio_add_eq_sum_Iic (f := fun j : Fin n => f j + 4) i).symm

private lemma gap_prefix_top {n : ℕ} (f : Fin n → ℕ) :
    gapPrefix f n = (∑ i, f i) + 4 * n := by
  have hs : (Finset.univ.filter (fun j : Fin n => j.val < n)) = Finset.univ :=
    Finset.filter_true_of_mem (fun j _ => j.isLt)
  change (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < n), (f j + 4)) = _
  rw [hs, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.mul_comm n 4]

private lemma boundary_composition (L n : ℕ) (s : Fin (n + 1) → ℕ)
    (hz : s 0 = 0) (ht : s (Fin.last n) = L)
    (hs : ∀ i : Fin n, s i.castSucc + 5 ≤ s i.succ) :
    ∃! f : PositiveLengths (L - 4 * n) n,
      ∀ i : Fin (n + 1), gapPrefix f.val i.val = s i := by
  classical
  let f : Fin n → ℕ := fun i => s i.succ - s i.castSucc - 4
  have hf (i : Fin n) : 0 < f i := by
    have h := hs i
    dsimp only [f]
    omega
  have he : ∀ i : Fin (n + 1), gapPrefix f i.val = s i := by
    intro i
    let F : ℕ → ℕ := fun k => s ⟨min k n, by omega⟩
    have hstrict : StrictMono s := Fin.strictMono_iff_lt_succ.mpr (by
      intro j
      have h := hs j
      omega)
    have hmono : Monotone s := hstrict.monotone
    have hF : Monotone F := by
      intro a b hab
      apply hmono
      apply Fin.le_def.mpr
      exact min_le_min hab (le_refl n)
    have hF_eq (k : ℕ) (hk : k ≤ n) : F k = s ⟨k, by omega⟩ := by
      dsimp only [F]
      apply congrArg s
      apply Fin.ext
      simp [Nat.min_eq_left hk]
    have hstep (j : Fin n) : F (j.val + 1) - F j.val = f j + 4 := by
      have h1 : F (j.val + 1) = s j.succ := by
        rw [hF_eq (j.val + 1) (by omega)]
        apply congrArg s
        apply Fin.ext
        rfl
      have h0 : F j.val = s j.castSucc := by
        rw [hF_eq j.val (by omega)]
        apply congrArg s
        apply Fin.ext
        rfl
      rw [h1, h0]
      dsimp only [f]
      have h := hs j
      omega
    have hsum := Finset.sum_range_tsub hF i.val
    have hsum' : gapPrefix f i.val = F i.val - F 0 := by
      rw [show gapPrefix f i.val = ∑ j ∈ Finset.range i.val,
          (F (j + 1) - F j) by
        apply Finset.sum_bij (fun j _ => j.val)
        · intro j hj
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
        · intro a ha b hb h
          exact Fin.ext h
        · intro b hb
          have hb' := Finset.mem_range.mp hb
          refine ⟨⟨b, by omega⟩, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        · intro j hj
          rw [hstep j]]
      exact hsum
    rw [hsum']
    have hi : F i.val = s i := by
      rw [hF_eq i.val (by omega)]
    have hzero : F 0 = s 0 := by
      rw [hF_eq 0 (by omega)]
      congr 1
    rw [hi, hzero, hz]
    simp
  have hsum : ∑ i, f i = L - 4 * n := by
    have h := he (Fin.last n)
    rw [Fin.val_last, gap_prefix_top, ht] at h
    omega
  refine ⟨⟨f, hf, hsum⟩, he, ?_⟩
  intro g hg
  apply Subtype.ext
  funext i
  have hgi := hg i.castSucc
  have hgj := hg i.succ
  simp only [Fin.val_castSucc] at hgi
  rw [Fin.val_succ, gap_prefix_step, hgi] at hgj
  change g.val i = f i
  dsimp only [f]
  omega

private lemma composition_gap_prefix (L n : ℕ) (hbound : 5 * n ≤ L)
    (f : PositiveLengths (L - 4 * n) n) :
    gapPrefix f.val 0 = 0 ∧ gapPrefix f.val n = L ∧
      (∀ i : Fin n, gapPrefix f.val i.val + 5 ≤ gapPrefix f.val (i.val + 1)) ∧
      StrictMono (fun i : Fin (n + 1) => gapPrefix f.val i.val) := by
  have hz : gapPrefix f.val 0 = 0 := by
    rw [gapPrefix.eq_1]
    simp only [Nat.not_lt_zero, Finset.filter_false, Finset.sum_empty]
  have ht : gapPrefix f.val n = L := by
    rw [gap_prefix_top, f.property.2]
    omega
  have hs (i : Fin n) : gapPrefix f.val i.val + 5 ≤ gapPrefix f.val (i.val + 1) := by
    rw [gap_prefix_step]
    have hp := f.property.1 i
    omega
  refine ⟨hz, ht, hs, Fin.strictMono_iff_lt_succ.mpr ?_⟩
  intro i
  have h := hs i
  simp only [Fin.val_castSucc, Fin.val_succ]
  exact lt_of_lt_of_le (by omega) h

private lemma admissible_sub_iff (L : ℕ) (B : Finset (Fin L)) :
    Admissible L B ↔ ∀ a ∈ B, ∀ b ∈ B, a ≠ b → 5 ≤ (b - a).val := by
  have he (a b : Fin L) (hne : a ≠ b) :
      (if a.val < b.val then b.val - a.val else L + b.val - a.val) = (b - a).val := by
    by_cases h : a.val < b.val
    · rw [ite_eq_left h, Fin.sub_val_of_le (show a ≤ b from Nat.le_of_lt h)]
    · have hba : b < a := by
        have hn : a.val ≠ b.val := fun h => hne (Fin.ext h)
        exact show b.val < a.val by omega
      rw [ite_eq_right h, Fin.coe_sub_iff_lt.mpr hba]
  constructor <;> intro h a ha b hb hne
  · exact (he a b hne) ▸ h a ha b hb hne
  · exact (he a b hne).symm ▸ h a ha b hb hne

private lemma admissible_translate (L : ℕ) [NeZero L] (B : Finset (Fin L)) (a : Fin L) :
    Admissible L (B.image (fun b => b + a)) ↔ Admissible L B := by
  classical
  rw [admissible_sub_iff, admissible_sub_iff]
  change (↑(B.image (fun b => b + a)) : Set (Fin L)).Pairwise _ ↔
    (B : Set (Fin L)).Pairwise _
  rw [Finset.coe_image, (add_left_injective a).injOn.pairwise_image]
  simp only [Set.Pairwise, Function.onFun, add_sub_add_right_eq_sub]

private def rootedEmbedding (L n : ℕ) (hbound : 5 * n ≤ L)
    (f : PositiveLengths (L - 4 * n) n) : Fin n ↪o Fin L := by
  have hp := composition_gap_prefix L n hbound f
  refine OrderEmbedding.ofStrictMono
    (fun i => ⟨gapPrefix f.val i.val, ?_⟩) ?_
  · have h := hp.2.2.2 i.castSucc_lt_last
    simpa only [Fin.val_castSucc, Fin.val_last, hp.2.1] using h
  · intro i j hij
    have h := hp.2.2.2 (show i.castSucc < j.castSucc from hij)
    exact show gapPrefix f.val i.val < gapPrefix f.val j.val from
      (by simpa only [Fin.val_castSucc] using h)

private def rootedSet (L n : ℕ) (hbound : 5 * n ≤ L)
    (f : PositiveLengths (L - 4 * n) n) : Finset (Fin L) :=
  Finset.univ.map (rootedEmbedding L n hbound f).toEmbedding

private lemma rooted_properties (L n : ℕ) [NeZero L] (hn : 1 ≤ n)
    (hbound : 5 * n ≤ L) (f : PositiveLengths (L - 4 * n) n) :
    (rootedSet L n hbound f).card = n ∧
      Admissible L (rootedSet L n hbound f) ∧ 0 ∈ rootedSet L n hbound f := by
  classical
  have hp := composition_gap_prefix L n hbound f
  refine ⟨?_, ?_, ?_⟩
  · change (Finset.univ.map (rootedEmbedding L n hbound f).toEmbedding).card = n
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro a ha b hb hne
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hb
    subst a
    subst b
    change 5 ≤ if gapPrefix f.val i.val < gapPrefix f.val j.val then
      gapPrefix f.val j.val - gapPrefix f.val i.val else
      L + gapPrefix f.val j.val - gapPrefix f.val i.val
    split_ifs with hij
    · have hij' : i.val < j.val := by
        have h := (hp.2.2.2.lt_iff_lt (a := i.castSucc) (b := j.castSucc)).mp hij
        exact show i.val < j.val from h
      have hnext := hp.2.2.2.monotone (show i.succ ≤ j.castSucc by
        exact show i.val + 1 ≤ j.val by omega)
      have hstep := hp.2.2.1 i
      simp only [Fin.val_succ, Fin.val_castSucc] at hnext
      omega
    · have hnext := hp.2.2.2.monotone (Fin.le_last i.succ)
      have hstep := hp.2.2.1 i
      simp only [Fin.val_succ, Fin.val_last, hp.2.1] at hnext
      omega
  · apply Finset.mem_map.mpr
    refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    exact hp.1

private lemma rooted_injective (L n : ℕ) (hbound : 5 * n ≤ L) :
    Function.Injective (rootedSet L n hbound) := by
  intro f g hfg
  have hp := composition_gap_prefix L n hbound f
  have hq := composition_gap_prefix L n hbound g
  have hc : (rootedSet L n hbound f).card = n := by
    change (Finset.univ.map (rootedEmbedding L n hbound f).toEmbedding).card = n
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have he (u : PositiveLengths (L - 4 * n) n)
      (hu : rootedSet L n hbound u = rootedSet L n hbound f) :
      rootedEmbedding L n hbound u = (rootedSet L n hbound f).orderEmbOfFin hc := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    rw [← hu]
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have heq := (he f rfl).trans (he g hfg.symm).symm
  apply Subtype.ext
  funext i
  have hval (j : Fin n) : gapPrefix f.val j.val = gapPrefix g.val j.val :=
    congrArg Fin.val (DFunLike.congr_fun heq j)
  have hs : gapPrefix f.val (i.val + 1) = gapPrefix g.val (i.val + 1) := by
    by_cases hi : i.val + 1 < n
    · exact hval ⟨i.val + 1, hi⟩
    · have hi' : i.val + 1 = n := by omega
      rw [hi', hp.2.1, hq.2.1]
  rw [gap_prefix_step, gap_prefix_step, hval i] at hs
  omega

private lemma rooted_surjective (L n : ℕ) [NeZero L] (hL : 5 ≤ L) (hn : 1 ≤ n)
    (hbound : 5 * n ≤ L) (S : Finset (Fin L)) (hc : S.card = n)
    (hS : Admissible L S) (hzero : 0 ∈ S) :
    ∃ f : PositiveLengths (L - 4 * n) n, rootedSet L n hbound f = S := by
  classical
  let e := S.orderEmbOfFin hc
  have ez : e ⟨0, by omega⟩ = 0 := by
    change S.orderEmbOfFin hc ⟨0, by omega⟩ = 0
    rw [Finset.orderEmbOfFin_zero hc (by omega)]
    exact le_antisymm (Finset.min'_le S 0 hzero) (Fin.zero_le _)
  let s : Fin (n + 1) → ℕ := fun i =>
    if h : i.val < n then (e ⟨i.val, h⟩).val else L
  have hcast (i : Fin n) : s i.castSucc = (e i).val := by
    dsimp only [s, Fin.val_castSucc]
    rw [dite_eq_left i.isLt]
  have hz : s 0 = 0 := by
    dsimp only [s]
    rw [dite_eq_left (show (0 : Fin (n + 1)).val < n from (by exact Nat.zero_lt_of_lt hn))]
    exact congrArg Fin.val ez
  have ht : s (Fin.last n) = L := by
    dsimp only [s, Fin.val_last]
    rw [dite_eq_right (by omega)]
  have hs (i : Fin n) : s i.castSucc + 5 ≤ s i.succ := by
    rw [hcast]
    by_cases hi : i.val + 1 < n
    · have hv : s i.succ = (e ⟨i.val + 1, hi⟩).val := by
        dsimp only [s, Fin.val_succ]
        rw [dite_eq_left hi]
      rw [hv]
      have hlt : e i < e ⟨i.val + 1, hi⟩ := e.strictMono (by exact Nat.lt_succ_self _)
      have h := hS (e i) (S.orderEmbOfFin_mem hc i)
        (e ⟨i.val + 1, hi⟩) (S.orderEmbOfFin_mem hc _) (ne_of_lt hlt)
      rw [ite_eq_left (show (e i).val < (e ⟨i.val + 1, hi⟩).val from hlt)] at h
      omega
    · have hv : s i.succ = L := by
        dsimp only [s, Fin.val_succ]
        rw [dite_eq_right hi]
      rw [hv]
      by_cases hez : e i = 0
      · rw [hez, Fin.val_zero]
        omega
      · have h := hS (e i) (S.orderEmbOfFin_mem hc i) 0 hzero hez
        rw [Fin.val_zero, ite_eq_right (by omega)] at h
        omega
  obtain ⟨f, hf, _⟩ := boundary_composition L n s hz ht hs
  refine ⟨f, ?_⟩
  have heq : rootedEmbedding L n hbound f = e := by
    apply DFunLike.ext
    intro i
    apply Fin.ext
    change gapPrefix f.val i.val = (e i).val
    have h := hf i.castSucc
    rw [hcast] at h
    simpa only [Fin.val_castSucc] using h
  change Finset.univ.map (rootedEmbedding L n hbound f).toEmbedding = S
  rw [heq]
  exact S.map_orderEmbOfFin_univ hc

private noncomputable def marked_gap_equiv (L n : ℕ) (hL : 5 ≤ L)
    (hn : 1 ≤ n) (hbound : 5 * n ≤ L) :
    (Σ B : {B // B ∈ placements L n}, {a // a ∈ B.val}) ≃
      Fin L × PositiveLengths (L - 4 * n) n := by
  classical
  letI : NeZero L := ⟨by omega⟩
  let F : (Fin L × PositiveLengths (L - 4 * n) n) →
      (Σ B : {B // B ∈ placements L n}, {a // a ∈ B.val}) := fun p =>
    ⟨⟨(rootedSet L n hbound p.2).image (fun b => b + p.1), by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · exact (admissible_translate L _ p.1).mpr
            (rooted_properties L n hn hbound p.2).2.1
        · rw [Finset.card_image_of_injective _ (add_left_injective p.1)]
          exact (rooted_properties L n hn hbound p.2).1⟩,
      ⟨p.1, Finset.mem_image.mpr
        ⟨0, (rooted_properties L n hn hbound p.2).2.2, zero_add p.1⟩⟩⟩
  apply Equiv.symm
  apply Equiv.ofBijective F
  constructor
  · rintro ⟨a, f⟩ ⟨b, g⟩ he
    have ha := congrArg (fun p => p.2.val) he
    change a = b at ha
    subst b
    have hb := congrArg (fun p => p.1.val) he
    change (rootedSet L n hbound f).image (fun b => b + a) =
      (rootedSet L n hbound g).image (fun b => b + a) at hb
    have hs := Finset.image_injective (add_left_injective a) hb
    exact Prod.ext rfl (rooted_injective L n hbound hs)
  · intro p
    let S := p.1.val.image (fun b => b - p.2.val)
    have hpc := (Finset.mem_filter.mp p.1.property).2
    have hc : S.card = n := by
      dsimp only [S]
      rw [Finset.card_image_of_injective _ (fun _ _ h => sub_left_injective h)]
      exact hpc.2
    have hS : Admissible L S := by
      change Admissible L (p.1.val.image (fun b => b - p.2.val))
      have h := (admissible_translate L p.1.val (-p.2.val)).mpr hpc.1
      simpa only [sub_eq_add_neg] using h
    have hz : (0 : Fin L) ∈ S :=
      Finset.mem_image.mpr ⟨p.2.val, p.2.property, sub_self _⟩
    obtain ⟨f, hf⟩ := rooted_surjective L n hL hn hbound S hc hS hz
    refine ⟨(p.2.val, f), ?_⟩
    have hb : (F (p.2.val, f)).1.val = p.1.val := by
      change (rootedSet L n hbound f).image (fun b => b + p.2.val) = p.1.val
      rw [hf]
      change (p.1.val.image (fun b => b - p.2.val)).image (fun b => b + p.2.val) = _
      rw [Finset.image_image]
      rw [show ((fun b : Fin L => b + p.2.val) ∘ fun b => b - p.2.val) = id from
        funext (fun b => sub_add_cancel b p.2.val), Finset.image_id]
    apply Sigma.ext (Subtype.ext hb)
    apply (Subtype.heq_iff_coe_eq (fun a => by rw [hb])).mpr
    rfl

private lemma marked_count (L n : ℕ) (hL : 5 ≤ L) (hn : 1 ≤ n)
    (hbound : 5 * n ≤ L) :
    n * (placements L n).card = L * (L - 4 * n - 1).choose (n - 1) := by
  classical
  have hc := Nat.card_congr (marked_gap_equiv L n hL hn hbound)
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin L), Fintype.card_fin,
    positive_lengths_card (L - 4 * n) n hn (by omega), Nat.card_eq_fintype_card,
    Fintype.card_sigma] at hc
  have hs : (∑ B : {B // B ∈ placements L n}, Fintype.card {a // a ∈ B.val}) =
      (placements L n).card * n := by
    have hb (B : {B // B ∈ placements L n}) : B.val.card = n :=
      (Finset.mem_filter.mp B.property).2.2
    simp only [Fintype.card_coe, hb, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, smul_eq_mul]
  rw [hs, Nat.mul_comm] at hc
  exact hc

private lemma placement_count (L n : ℕ) (hL : 5 ≤ L) (hn : 1 ≤ n)
    (hbound : 5 * n ≤ L) :
    (placements L n).card = L * (L - 4 * n - 1).choose (n - 1) / n ∧
      n ∣ L * (L - 4 * n - 1).choose (n - 1) := by
  have hc := marked_count L n hL hn hbound
  constructor
  · rw [← hc, Nat.mul_div_right _ (by omega : 0 < n)]
  · exact ⟨(placements L n).card, hc.symm⟩

private lemma label_count (L : ℕ) (B : Finset (Fin L)) (E : ℤ) :
    (B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E)).card =
      if ((B.card : ℤ) + E) % 2 = 0 ∧ |E| ≤ (B.card : ℤ) then
        B.card.choose (((B.card : ℤ) + E) / 2).toNat else 0 := by
  classical
  split_ifs with h
  · have hbounds := abs_le.mp h.2
    have he (k : ℕ) : 2 * (k : ℤ) - B.card = E ↔
        k = (((B.card : ℤ) + E) / 2).toNat := by
      omega
    rw [Finset.filter_congr (fun x _ => he x.card), ← Finset.powersetCard_eq_filter,
      Finset.card_powersetCard]
  · apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx he
    have hc := Finset.card_le_card (Finset.mem_powerset.mp hx)
    apply h
    refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩⟩ <;> omega

private lemma vacuum_count (L : ℕ) (E : ℤ) :
    ∑ B ∈ placements L 0,
      (B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E)).card =
        if E = 0 then 1 else 0 := by
  classical
  have hp : placements L 0 = {∅} := by
    ext B
    simp only [placements, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.card_eq_zero, Finset.mem_singleton]
    constructor
    · exact And.right
    · intro h
      subst B
      exact ⟨by intro a ha; exact False.elim (Finset.notMem_empty a ha), rfl⟩
  rw [hp, Finset.sum_singleton, label_count]
  by_cases h : E = 0
  · subst E
    simp
  · simp [h]

private lemma sum_by_size (L : ℕ) (hL : 5 ≤ L) (E : ℤ) :
    bubbleCount L E = (if E = 0 then 1 else 0) +
      ∑ n ∈ Finset.Icc 1 (L / 5),
        (placements L n).card *
          (if ((n : ℤ) + E) % 2 = 0 ∧ |E| ≤ (n : ℤ) then
            n.choose (((n : ℤ) + E) / 2).toNat else 0) := by
  classical
  let S := (Finset.univ : Finset (Finset (Fin L))).filter (Admissible L)
  let f := fun B : Finset (Fin L) =>
    (B.powerset.filter (fun x => 2 * (x.card : ℤ) - B.card = E)).card
  have hm : ∀ B ∈ S, B.card ∈ Finset.Icc 0 (L / 5) := by
    intro B hB
    have hb := packing_bound L hL B (Finset.mem_filter.mp hB).2
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
  have hp (n : ℕ) : S.filter (fun B => B.card = n) = placements L n := by
    rw [placements.eq_1]
    exact Finset.filter_filter (Admissible L) (fun B => B.card = n) _
  have hs : bubbleCount L E =
      ∑ n ∈ Finset.Icc 0 (L / 5), ∑ B ∈ placements L n, f B := by
    change (∑ B ∈ S, f B) = _
    rw [← Finset.sum_fiberwise_of_maps_to hm f]
    simp only [hp]
  rw [hs, ← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le (L / 5)),
    Finset.sum_insert (by simp), show (Order.succ (0 : ℕ)) = 1 from rfl]
  rw [show (∑ B ∈ placements L 0, f B) = (if E = 0 then 1 else 0) from
    vacuum_count L E]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hb (B : Finset (Fin L)) (hB : B ∈ placements L n) : B.card = n :=
    (Finset.mem_filter.mp hB).2.2
  calc
    (∑ B ∈ placements L n, f B) = ∑ _B ∈ placements L n,
        (if ((n : ℤ) + E) % 2 = 0 ∧ |E| ≤ (n : ℤ) then
          n.choose (((n : ℤ) + E) / 2).toNat else 0) := by
      apply Finset.sum_congr rfl
      intro B hB
      dsimp only [f]
      rw [label_count, hb B hB]
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]

theorem result : claim := by
  intro L hL E
  rw [sum_by_size L hL E]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hnL⟩ := Finset.mem_Icc.mp hn
  rw [(placement_count L n hL hn1 (by omega)).1]

end D5.S3.Quantum.SpinChains.BubbleEigenstateDegeneracy
