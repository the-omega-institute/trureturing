/- GID: D5/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PatternAvoidance/ArcherBourneDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The 312/321 avoiders are exactly the rotation sums indexed by compositions. -/

import D5.S1.Words.Patterns.DerangementRatioNonconvergence
import D5.S3.ConceptDynamics.PatternAvoidance.RotationSumPowerPatternAvoidance
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Finite

open scoped BigOperators

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.PatternAvoidance.ArcherBourneDecomposition

open D5.S1.Words.Patterns.DerangementRatioNonconvergence
open D5.S3.ConceptDynamics.PatternAvoidance.RotationSumPowerPatternAvoidance

/-- The permutation pattern `312`, in zero-based value notation `[2, 0, 1]`. -/
noncomputable def pattern312 : Equiv.Perm (Fin 3) := Equiv.ofBijective (fun i : Fin 3 => ![2, 0, 1] i) (by decide)

/-- The permutation pattern `321`, in zero-based value notation `[2, 1, 0]`. -/
noncomputable def pattern321 : Equiv.Perm (Fin 3) := Equiv.ofBijective (fun i : Fin 3 => ![2, 1, 0] i) (by decide)

/-- Avoidance of `312`, specialized from the frozen generic pattern-containment predicate. -/
def Avoids312 {n : Nat} (pi : Equiv.Perm (Fin n)) : Prop := ¬Contains pattern312 pi

/-- Avoidance of `321`, specialized from the frozen generic pattern-containment predicate. -/
def Avoids321 {n : Nat} (pi : Equiv.Perm (Fin n)) : Prop := ¬Contains pattern321 pi

private lemma contains312_iff {n : Nat} (pi : Equiv.Perm (Fin n)) :
    Contains pattern312 pi <->
      exists a b c, a < b /\ b < c /\ pi b < pi c /\ pi c < pi a := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide), ?_, ?_⟩
    · exact (hf 1 2).mp (by decide)
    · exact (hf 2 0).mp (by decide)
  · rintro ⟨a, b, c, hab, hbc, hbcv, hcav⟩
    refine ⟨OrderEmbedding.ofStrictMono ![a, b, c] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          Fin.reduceFinMk, Matrix.cons_val] <;> omega), ?_⟩
    intro i j
    change pattern312 i < pattern312 j <->
      pi (![a, b, c] i) < pi (![a, b, c] j)
    fin_cases i <;> fin_cases j <;>
      simp [pattern312] <;> omega

private lemma contains321_iff {n : Nat} (pi : Equiv.Perm (Fin n)) :
    Contains pattern321 pi <->
      exists a b c, a < b /\ b < c /\ pi c < pi b /\ pi b < pi a := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide), ?_, ?_⟩
    · exact (hf 2 1).mp (by decide)
    · exact (hf 1 0).mp (by decide)
  · rintro ⟨a, b, c, hab, hbc, hcbv, hbav⟩
    refine ⟨OrderEmbedding.ofStrictMono ![a, b, c] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          Fin.reduceFinMk, Matrix.cons_val] <;> omega), ?_⟩
    intro i j
    change pattern321 i < pattern321 j <->
      pi (![a, b, c] i) < pi (![a, b, c] j)
    fin_cases i <;> fin_cases j <;>
      simp [pattern321] <;> omega

private abbrev Position (d : List Nat) := Sigma fun i : Fin d.length => Fin (d.get i)

private def Before {d : List Nat} (p q : Position d) : Prop :=
  p.1.val < q.1.val ∨ (p.1.val = q.1.val ∧ p.2.val < q.2.val)

private def taggedRotate (d : List Nat) (p : Position d) : Position d :=
  ⟨p.1, ⟨(p.2.val + 1) % d.get p.1, by
    exact Nat.mod_lt _ (Nat.zero_lt_of_lt p.2.isLt)⟩⟩

private lemma before_block_le {d : List Nat} {p q : Position d} (h : Before p q) :
    p.1.val ≤ q.1.val := by
  rcases h with h | h
  · omega
  · omega

private lemma before_trans {d : List Nat} {p q r : Position d}
    (hpq : Before p q) (hqr : Before q r) : Before p r := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  rcases r with ⟨k, z⟩
  dsimp only [Before] at hpq hqr ⊢
  by_cases hik : i.val < k.val
  · exact Or.inl hik
  · right
    have hik' : i.val = k.val := by
      rcases hpq with hpq | ⟨hpq, _⟩ <;>
        rcases hqr with hqr | ⟨hqr, _⟩ <;> omega
    have hidx : i = k := Fin.ext hik'
    subst k
    rcases hpq with hpq | ⟨hpq, hxy⟩ <;>
      rcases hqr with hqr | ⟨hqr, hyz⟩ <;> omega

private lemma descent_same_block {d : List Nat} {p q : Position d}
    (hpq : Before p q)
    (hdesc : Before (taggedRotate d q) (taggedRotate d p)) :
    p.1 = q.1 := by
  apply Fin.ext
  have h₁ := before_block_le hpq
  have h₂ := before_block_le hdesc
  change q.1.val ≤ p.1.val at h₂
  omega

private lemma taggedRotate_apply (d : List Nat) (p : Position d) :
    (Equiv.Perm.sigmaCongrRight fun i => finRotate (d.get i)) p = taggedRotate d p := by
  rcases p with ⟨i, x⟩
  change (⟨i, finRotate (d.get i) x⟩ : Position d) =
    ⟨i, ⟨(x.val + 1) % d.get i, _⟩⟩
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Fin.ext
  simp [finRotate_apply, Fin.add_def]

private lemma rotationSumPerm_apply_tagged (d : List Nat) (p : Position d) :
    rotationSumPerm d ((@finSigmaFinEquiv d.length (fun i => d.get i)) p) =
      (@finSigmaFinEquiv d.length (fun i => d.get i)) (taggedRotate d p) := by
  simp only [rotationSumPerm, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact congrArg _ (taggedRotate_apply d p)

private def TaggedContains312 (d : List Nat) : Prop :=
  ∃ a b c,
    Before a b ∧ Before b c ∧
    Before (taggedRotate d b) (taggedRotate d c) ∧
    Before (taggedRotate d c) (taggedRotate d a)

private def TaggedContains321 (d : List Nat) : Prop :=
  ∃ a b c,
    Before a b ∧ Before b c ∧
    Before (taggedRotate d c) (taggedRotate d b) ∧
    Before (taggedRotate d b) (taggedRotate d a)

private def blockOffset (d : List Nat) (k : Nat) : Nat :=
  ∑ x ∈ Finset.range k, d.getD x 0

private lemma blockOffset_succ (d : List Nat) (k : Nat) :
    blockOffset d (k + 1) = blockOffset d k + d.getD k 0 := by
  simp [blockOffset, Finset.sum_range_succ]

private lemma finSigmaFinEquiv_val (d : List Nat) (p : Position d) :
    ((@finSigmaFinEquiv d.length (fun i => d.get i)) p : Nat) =
      blockOffset d p.1.val + p.2.val := by
  rw [finSigmaFinEquiv_apply]
  simp only [blockOffset]
  rw [← Fin.sum_univ_eq_sum_range (fun x => d.getD x 0) p.1.val]
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (k.isLt.trans p.1.isLt)]
  simp only [Option.getD_some, List.get_eq_getElem]
  rfl

private lemma blockOffset_add_block_le {d : List Nat} {i j : Fin d.length}
    (hij : i.val < j.val) :
    blockOffset d i.val + d.get i ≤ blockOffset d j.val := by
  have hi : d.getD i.val 0 = d.get i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt]
    simp [List.get_eq_getElem]
  have hfirst : blockOffset d i.val + d.get i = blockOffset d (i.val + 1) := by
    rw [blockOffset_succ, hi]
  have hle : i.val + 1 ≤ j.val := by omega
  have hs := Finset.sum_range_add_sum_Ico (fun x => d.getD x 0) hle
  change blockOffset d (i.val + 1) +
    (∑ k ∈ Finset.Ico (i.val + 1) j.val, d.getD k 0) = blockOffset d j.val at hs
  rw [hfirst, ← hs]
  exact Nat.le_add_right _ _

private lemma before_iff_fin_lt {d : List Nat} (p q : Position d) :
    Before p q ↔
      (@finSigmaFinEquiv d.length (fun i => d.get i)) p <
        (@finSigmaFinEquiv d.length (fun i => d.get i)) q := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  change (i.val < j.val ∨ (i.val = j.val ∧ x.val < y.val)) ↔ _
  rw [Fin.lt_def, finSigmaFinEquiv_val, finSigmaFinEquiv_val]
  dsimp only
  constructor
  · rintro (hij | ⟨hij, hxy⟩)
    · have hbound := blockOffset_add_block_le hij
      have hxLt : x.val < d.get i := x.isLt
      omega
    · have hidx : i = j := Fin.ext hij
      subst j
      omega
  · intro hlt
    by_cases hij : i.val < j.val
    · exact Or.inl hij
    by_cases hji : j.val < i.val
    · have hbound := blockOffset_add_block_le hji
      have hyLt : y.val < d.get j := y.isLt
      omega
    · right
      have hidx : i = j := Fin.ext (by omega)
      subst j
      exact ⟨rfl, by omega⟩

private lemma contains312_iff_tagged {d : List Nat} :
    Contains pattern312 (rotationSumPerm d) ↔ TaggedContains312 d := by
  rw [contains312_iff]
  let flatten := @finSigmaFinEquiv d.length (fun i => d.get i)
  constructor
  · rintro ⟨a, b, c, hab, hbc, hbcv, hcav⟩
    let pa := flatten.symm a
    let pb := flatten.symm b
    let pc := flatten.symm c
    refine ⟨pa, pb, pc, ?_, ?_, ?_, ?_⟩
    · apply (before_iff_fin_lt pa pb).mpr
      simpa [pa, pb, flatten] using hab
    · apply (before_iff_fin_lt pb pc).mpr
      simpa [pb, pc, flatten] using hbc
    · apply (before_iff_fin_lt (taggedRotate d pb) (taggedRotate d pc)).mpr
      rw [← rotationSumPerm_apply_tagged, ← rotationSumPerm_apply_tagged]
      simpa [pa, pb, pc, flatten] using hbcv
    · apply (before_iff_fin_lt (taggedRotate d pc) (taggedRotate d pa)).mpr
      rw [← rotationSumPerm_apply_tagged, ← rotationSumPerm_apply_tagged]
      simpa [pa, pb, pc, flatten] using hcav
  · rintro ⟨a, b, c, hab, hbc, hbcv, hcav⟩
    refine ⟨flatten a, flatten b, flatten c, ?_, ?_, ?_, ?_⟩
    · exact (before_iff_fin_lt a b).mp hab
    · exact (before_iff_fin_lt b c).mp hbc
    · rw [rotationSumPerm_apply_tagged, rotationSumPerm_apply_tagged]
      exact (before_iff_fin_lt (taggedRotate d b) (taggedRotate d c)).mp hbcv
    · rw [rotationSumPerm_apply_tagged, rotationSumPerm_apply_tagged]
      exact (before_iff_fin_lt (taggedRotate d c) (taggedRotate d a)).mp hcav

private lemma contains321_iff_tagged {d : List Nat} :
    Contains pattern321 (rotationSumPerm d) ↔ TaggedContains321 d := by
  rw [contains321_iff]
  let flatten := @finSigmaFinEquiv d.length (fun i => d.get i)
  constructor
  · rintro ⟨a, b, c, hab, hbc, hcbv, hbav⟩
    let pa := flatten.symm a
    let pb := flatten.symm b
    let pc := flatten.symm c
    refine ⟨pa, pb, pc, ?_, ?_, ?_, ?_⟩
    · apply (before_iff_fin_lt pa pb).mpr
      simpa [pa, pb, flatten] using hab
    · apply (before_iff_fin_lt pb pc).mpr
      simpa [pb, pc, flatten] using hbc
    · apply (before_iff_fin_lt (taggedRotate d pc) (taggedRotate d pb)).mpr
      rw [← rotationSumPerm_apply_tagged, ← rotationSumPerm_apply_tagged]
      simpa [pa, pb, pc, flatten] using hcbv
    · apply (before_iff_fin_lt (taggedRotate d pb) (taggedRotate d pa)).mpr
      rw [← rotationSumPerm_apply_tagged, ← rotationSumPerm_apply_tagged]
      simpa [pa, pb, pc, flatten] using hbav
  · rintro ⟨a, b, c, hab, hbc, hcbv, hbav⟩
    refine ⟨flatten a, flatten b, flatten c, ?_, ?_, ?_, ?_⟩
    · exact (before_iff_fin_lt a b).mp hab
    · exact (before_iff_fin_lt b c).mp hbc
    · rw [rotationSumPerm_apply_tagged, rotationSumPerm_apply_tagged]
      exact (before_iff_fin_lt (taggedRotate d c) (taggedRotate d b)).mp hcbv
    · rw [rotationSumPerm_apply_tagged, rotationSumPerm_apply_tagged]
      exact (before_iff_fin_lt (taggedRotate d b) (taggedRotate d a)).mp hbav

private lemma no312_mod_succ {m : Nat} (_hm : 0 < m)
    {x y z : Nat} (hx : x < m) (hy : y < m) (hz : z < m)
    (hxy : x < y) (hyz : y < z)
    (hyzv : (y + 1) % m < (z + 1) % m)
    (hxzv : (z + 1) % m < (x + 1) % m) : False := by
  have hxle : x + 1 ≤ m := by omega
  by_cases hxc : x + 1 < m
  · have hxm : (x + 1) % m = x + 1 := Nat.mod_eq_of_lt hxc
    by_cases hzc : z + 1 < m
    · have hzm : (z + 1) % m = z + 1 := Nat.mod_eq_of_lt hzc
      omega
    · have hzeq : z + 1 = m := by omega
      have hzm : (z + 1) % m = 0 := by simp [hzeq]
      omega
  · have hxeq : x + 1 = m := by omega
    omega

private lemma no321_mod_succ {m : Nat} (_hm : 0 < m)
    {x y z : Nat} (hx : x < m) (hy : y < m) (hz : z < m)
    (hxy : x < y) (hyz : y < z)
    (hyxv : (y + 1) % m < (x + 1) % m)
    (_hzyv : (z + 1) % m < (y + 1) % m) : False := by
  have hxle : x + 1 ≤ m := by omega
  by_cases hxc : x + 1 < m
  · have hxm : (x + 1) % m = x + 1 := Nat.mod_eq_of_lt hxc
    by_cases hyc : y + 1 < m
    · have hym : (y + 1) % m = y + 1 := Nat.mod_eq_of_lt hyc
      omega
    · have hyeq : y + 1 = m := by omega
      have hym : (y + 1) % m = 0 := by simp [hyeq]
      omega
  · have hxeq : x + 1 = m := by omega
    omega

private lemma tagged_no_312 {d : List Nat} (hpos : ∀ i : Fin d.length, 0 < d.get i) :
    ¬TaggedContains312 d := by
  rintro ⟨a, b, c, hab, hbc, hbcv, hcav⟩
  have hac : Before a c := before_trans hab hbc
  have hac_same : a.1 = c.1 := descent_same_block hac hcav
  have hab_same : a.1 = b.1 := by
    apply Fin.ext
    have h₁ := before_block_le hab
    have h₂ := before_block_le hbc
    have hEq := congrArg Fin.val hac_same
    omega
  rcases a with ⟨i, x⟩
  rcases b with ⟨j, y⟩
  rcases c with ⟨k, z⟩
  have hij : i = j := Fin.ext (congrArg Fin.val hab_same)
  have hik : i = k := Fin.ext (congrArg Fin.val hac_same)
  subst j
  subst k
  have hxy : x.val < y.val := by simpa [Before] using hab
  have hyz : y.val < z.val := by simpa [Before] using hbc
  have hyzv : (y.val + 1) % d.get i < (z.val + 1) % d.get i := by
    simpa [Before, taggedRotate] using hbcv
  have hxzv : (z.val + 1) % d.get i < (x.val + 1) % d.get i := by
    simpa [Before, taggedRotate] using hcav
  exact no312_mod_succ (hpos i) x.isLt y.isLt z.isLt hxy hyz hyzv hxzv

private lemma tagged_no_321 {d : List Nat} (hpos : ∀ i : Fin d.length, 0 < d.get i) :
    ¬TaggedContains321 d := by
  rintro ⟨a, b, c, hab, hbc, hcbv, hbav⟩
  have hab_same : a.1 = b.1 := descent_same_block hab hbav
  have hbc_same : b.1 = c.1 := descent_same_block hbc hcbv
  rcases a with ⟨i, x⟩
  rcases b with ⟨j, y⟩
  rcases c with ⟨k, z⟩
  have hij : i = j := Fin.ext (congrArg Fin.val hab_same)
  have hjk : j = k := Fin.ext (congrArg Fin.val hbc_same)
  subst j
  subst k
  have hxy : x.val < y.val := by simpa [Before] using hab
  have hyz : y.val < z.val := by simpa [Before] using hbc
  have hyxv : (y.val + 1) % d.get i < (x.val + 1) % d.get i := by
    simpa [Before, taggedRotate] using hbav
  have hzyv : (z.val + 1) % d.get i < (y.val + 1) % d.get i := by
    simpa [Before, taggedRotate] using hcbv
  exact no321_mod_succ (hpos i) x.isLt y.isLt z.isLt hxy hyz hyxv hzyv

/-- Every positive direct sum of cyclic rotations avoids both `312` and `321`. -/
theorem rotationSumPerm_avoids_312_321
    {d : List Nat} (hpos : ∀ i : Fin d.length, 0 < d.get i) :
    Avoids312 (rotationSumPerm d) ∧ Avoids321 (rotationSumPerm d) := by
  constructor
  · rw [Avoids312, contains312_iff_tagged]
    exact tagged_no_312 hpos
  · rw [Avoids321, contains321_iff_tagged]
    exact tagged_no_321 hpos

private theorem composition_index_sum {n : Nat} (c : Composition n) :
    (∑ i : Fin c.blocks.length, c.blocks.get i) = n := by
  change (∑ i : Fin c.length, c.blocksFun i) = n
  exact c.sum_blocksFun

/-- The frozen list-level rotation sum, transported along a composition's sum equation. -/
def rotationSumComposition {n : Nat} (c : Composition n) : Equiv.Perm (Fin n) :=
  (finCongr (composition_index_sum c)).permCongr (rotationSumPerm c.blocks)

private lemma contains_finCongr_permCongr_iff {k m n : Nat} (h : m = n)
    (sigma : Equiv.Perm (Fin k)) (pi : Equiv.Perm (Fin m)) :
    Contains sigma ((finCongr h).permCongr pi) ↔ Contains sigma pi := by
  subst n
  have hpi : (finCongr rfl).permCongr pi = pi := by
    ext x
    rfl
  rw [hpi]

private lemma contains_rotationSumComposition_iff {k n : Nat}
    (sigma : Equiv.Perm (Fin k)) (c : Composition n) :
    Contains sigma (rotationSumComposition c) ↔ Contains sigma (rotationSumPerm c.blocks) := by
  exact contains_finCongr_permCongr_iff (composition_index_sum c) sigma _

/-- Every composition indexes a permutation avoiding both `312` and `321`. -/
theorem rotationSumComposition_avoids_312_321 {n : Nat} (c : Composition n) :
    Avoids312 (rotationSumComposition c) ∧ Avoids321 (rotationSumComposition c) := by
  have hpos : ∀ i : Fin c.blocks.length, 0 < c.blocks.get i :=
    fun i => c.blocks_pos (List.get_mem c.blocks i)
  have h := rotationSumPerm_avoids_312_321 hpos
  simpa only [Avoids312, Avoids321, contains_rotationSumComposition_iff] using h

private lemma blockOffset_eq_sizeUpTo {n : Nat} (c : Composition n) (k : Nat)
    (hk : k ≤ c.length) : blockOffset c.blocks k = c.sizeUpTo k := by
  induction k with
  | zero => simp [blockOffset, Composition.sizeUpTo]
  | succ k ih =>
      have hklt : k < c.length := by omega
      rw [blockOffset_succ, c.sizeUpTo_succ hklt, ih hklt.le]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklt]
      simp only [Option.getD_some]

private lemma composition_flatten_eq_blocksFinEquiv {n : Nat} (c : Composition n) :
    (@finSigmaFinEquiv c.blocks.length (fun i => c.blocks.get i)).trans
      (finCongr (composition_index_sum c)) = c.blocksFinEquiv := by
  apply Equiv.ext
  intro p
  apply Fin.ext
  simp only [Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    Composition.blocksFinEquiv]
  rw [finSigmaFinEquiv_apply]
  congr 1
  rw [← blockOffset_eq_sizeUpTo c p.1.val p.1.isLt.le]
  simp only [blockOffset]
  rw [← Fin.sum_univ_eq_sum_range (fun x => c.blocks.getD x 0) p.1.val]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (k.isLt.trans p.1.isLt)]
  simp only [Option.getD_some, List.get_eq_getElem]
  rfl

private lemma rotationSumComposition_eq_blocksFinEquiv {n : Nat} (c : Composition n) :
    rotationSumComposition c =
      (c.blocksFinEquiv.symm.trans
        (Equiv.Perm.sigmaCongrRight fun i => finRotate (c.blocksFun i))).trans
        c.blocksFinEquiv := by
  let flatten := @finSigmaFinEquiv c.blocks.length (fun i => c.blocks.get i)
  let cast := finCongr (composition_index_sum c)
  let rotate := Equiv.Perm.sigmaCongrRight fun i => finRotate (c.blocks.get i)
  have he : flatten.trans cast = c.blocksFinEquiv :=
    composition_flatten_eq_blocksFinEquiv c
  have htransport : rotationSumComposition c = (flatten.trans cast).permCongr rotate := by
    ext x
    rfl
  calc
    rotationSumComposition c = (flatten.trans cast).permCongr rotate := htransport
    _ = c.blocksFinEquiv.permCongr rotate := congrArg (fun e => e.permCongr rotate) he
    _ = _ := rfl

private lemma rotationSumComposition_apply_blocksFinEquiv {n : Nat} (c : Composition n)
    (p : Sigma fun i : Fin c.length => Fin (c.blocksFun i)) :
    rotationSumComposition c (c.blocksFinEquiv p) =
      c.blocksFinEquiv ⟨p.1, finRotate (c.blocksFun p.1) p.2⟩ := by
  rw [rotationSumComposition_eq_blocksFinEquiv]
  simp

private lemma blocksFinEquiv_val {n : Nat} (c : Composition n)
    (p : Sigma fun i : Fin c.length => Fin (c.blocksFun i)) :
    (c.blocksFinEquiv p).val = c.sizeUpTo p.1.val + p.2.val := by
  exact c.coe_embedding p.1 p.2

private lemma prefix_lt_suffix {n : Nat} [NeZero n]
    {pi : Equiv.Perm (Fin n)} {z a b : Fin n}
    (hz : pi z = 0) (h312 : Avoids312 pi) (ha : a ≤ z) (hb : z < b) :
    pi a < pi b := by
  have hpb_ne : pi b ≠ 0 := by
    intro hpb
    have hbz : b = z := pi.injective (hpb.trans hz.symm)
    exact hb.ne hbz.symm
  rcases ha.eq_or_lt with rfl | haz
  · rw [hz]
    exact Fin.pos_iff_ne_zero.mpr hpb_ne
  · by_contra hnot
    have hp_ne : pi b ≠ pi a := by
      intro hp
      have hba : b = a := pi.injective hp
      subst b
      exact (not_lt_of_ge ha) hb
    have hba : pi b < pi a := lt_of_le_of_ne (not_lt.mp hnot) hp_ne
    have hzb : pi z < pi b := by
      rw [hz]
      exact Fin.pos_iff_ne_zero.mpr hpb_ne
    exact h312 ((contains312_iff pi).mpr ⟨a, z, b, haz, hb, hzb, hba⟩)

private lemma prefix_maps_prefix {n : Nat} [NeZero n]
    {pi : Equiv.Perm (Fin n)} {z a : Fin n}
    (hz : pi z = 0) (h312 : Avoids312 pi) (ha : a ≤ z) :
    pi a ≤ z := by
  classical
  let s : Finset (Fin n) := Finset.Iic z
  by_contra hnot
  have hza : z < pi a := lt_of_not_ge hnot
  have hmem : pi a ∈ s.image pi := by
    apply Finset.mem_image.mpr
    exact ⟨a, by simpa [s], rfl⟩
  have hnot_image_subset : ¬s.image pi ⊆ s := by
    intro hsub
    have := hsub hmem
    exact (not_le_of_gt hza) (by simpa [s] using this)
  have hcard : (s.image pi).card = s.card := Finset.card_image_of_injective s pi.injective
  have hnot_subset_image : ¬s ⊆ s.image pi := by
    intro hsub
    have heq : s = s.image pi :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
    apply hnot_image_subset
    rw [← heq]
  obtain ⟨x, hxs, hxnot⟩ := Finset.not_subset.mp hnot_subset_image
  obtain ⟨b, rfl⟩ := pi.surjective x
  have hzb : z < b := by
    by_contra hb
    apply hxnot
    exact Finset.mem_image.mpr ⟨b, by simpa [s] using not_lt.mp hb, rfl⟩
  have hab := prefix_lt_suffix hz h312 ha hzb
  have hpbz : pi b ≤ z := by simpa [s] using hxs
  exact (not_lt_of_ge hpbz) (hza.trans hab)

private lemma prefix_strictMono {n : Nat} [NeZero n]
    {pi : Equiv.Perm (Fin n)} {z a b : Fin n}
    (hz : pi z = 0) (h321 : Avoids321 pi) (_ha : a < z) (hb : b < z) (hab : a < b) :
    pi a < pi b := by
  by_contra hnot
  have hp_ne : pi b ≠ pi a := by
    intro hp
    exact hab.ne (pi.injective hp).symm
  have hba : pi b < pi a := lt_of_le_of_ne (not_lt.mp hnot) hp_ne
  have hpb_ne : pi b ≠ 0 := by
    intro hpb
    exact hb.ne (pi.injective (hpb.trans hz.symm))
  have hzb : pi z < pi b := by
    rw [hz]
    exact Fin.pos_iff_ne_zero.mpr hpb_ne
  exact h321 ((contains321_iff pi).mpr ⟨a, b, z, hab, hb, hzb, hba⟩)

private lemma prefix_apply {n : Nat} [NeZero n]
    {pi : Equiv.Perm (Fin n)} {z a : Fin n}
    (hz : pi z = 0) (h312 : Avoids312 pi) (h321 : Avoids321 pi) (ha : a < z) :
    (pi a).val = a.val + 1 := by
  let pos : Fin z.val → Fin n := fun i => ⟨i.val, i.isLt.trans z.isLt⟩
  have pos_lt (i : Fin z.val) : pos i < z := by
    exact i.isLt
  have image_ne_zero (i : Fin z.val) : pi (pos i) ≠ 0 := by
    intro hi
    exact (pos_lt i).ne (pi.injective (hi.trans hz.symm))
  let g : Fin z.val → Fin z.val := fun i =>
    ⟨(pi (pos i)).val - 1, by
      have hmap := prefix_maps_prefix hz h312 (pos_lt i).le
      have hpos := Fin.pos_iff_ne_zero.mpr (image_ne_zero i)
      have hmap' : (pi (pos i)).val ≤ z.val := hmap
      have hpos' : 0 < (pi (pos i)).val := hpos
      omega⟩
  have hg : StrictMono g := by
    intro i j hij
    have hpi := prefix_strictMono hz h321 (pos_lt i) (pos_lt j) hij
    have hi := Fin.pos_iff_ne_zero.mpr (image_ne_zero i)
    have hj := Fin.pos_iff_ne_zero.mpr (image_ne_zero j)
    exact show (pi (pos i)).val - 1 < (pi (pos j)).val - 1 by omega
  let i : Fin z.val := ⟨a.val, ha⟩
  have hfix := congrArg Fin.val (hg.apply_eq (x := i))
  have hpositive := Fin.pos_iff_ne_zero.mpr (image_ne_zero i)
  dsimp only [g] at hfix
  have hpos_i : pos i = a := by
    apply Fin.ext
    rfl
  rw [hpos_i] at hfix hpositive
  change (pi a).val = a.val + 1
  change 0 < (pi a).val at hpositive
  change (pi a).val - 1 = a.val at hfix
  omega

private def tailEquiv {n : Nat} (z : Fin n) :
    Fin (n - (z.val + 1)) ≃ {x : Fin n // z < x} where
  toFun i := ⟨⟨z.val + 1 + i.val, by
    have hz := z.isLt
    have hi := i.isLt
    omega⟩, by
      change z.val < z.val + 1 + i.val
      omega⟩
  invFun x := ⟨x.val.val - (z.val + 1), by
    have hz := z.isLt
    have hx := x.val.isLt
    have hzx : z.val < x.val.val := x.property
    omega⟩
  left_inv i := by
    apply Fin.ext
    dsimp
    omega
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    dsimp
    have hzx : z.val < x.val.val := x.property
    omega

private lemma tailEquiv_strictMono {n : Nat} (z : Fin n) :
    StrictMono (fun i => (tailEquiv z i).val) := by
  intro i j hij
  change z.val + 1 + i.val < z.val + 1 + j.val
  exact Nat.add_lt_add_left hij _

private lemma suffix_maps_suffix {n : Nat} [NeZero n]
    {pi : Equiv.Perm (Fin n)} {z x : Fin n}
    (hz : pi z = 0) (h312 : Avoids312 pi) (hx : z < x) :
    z < pi x := by
  classical
  by_contra hnot
  let s : Finset (Fin n) := Finset.Iic z
  have hmaps : ∀ y ∈ s, pi y ∈ s := by
    intro y hy
    have hyz : y ≤ z := by simpa [s] using hy
    simpa [s] using prefix_maps_prefix hz h312 hyz
  have hsymm : pi.symm (pi x) ∈ s :=
    Equiv.Perm.perm_symm_on_of_perm_on_finset hmaps (by
      simpa [s] using not_lt.mp hnot)
  rw [pi.symm_apply_apply] at hsymm
  exact (not_le_of_gt hx) (by simpa [s] using hsymm)

private def suffixPerm {n : Nat} (pi : Equiv.Perm (Fin n)) (z : Fin n)
    (htail : ∀ x, z < x → z < pi x) : Equiv.Perm (Fin (n - (z.val + 1))) :=
  (tailEquiv z).permCongr.symm (pi.subtypePermOfFintype htail)

private lemma suffixPerm_apply {n : Nat} (pi : Equiv.Perm (Fin n)) (z : Fin n)
    (htail : ∀ x, z < x → z < pi x) (i : Fin (n - (z.val + 1))) :
    pi (tailEquiv z i).val = (tailEquiv z (suffixPerm pi z htail i)).val := by
  have hsubtype :
      (pi.subtypePermOfFintype htail) (tailEquiv z i) =
        tailEquiv z (suffixPerm pi z htail i) := by
    change (pi.subtypePermOfFintype htail) (tailEquiv z i) =
      tailEquiv z ((tailEquiv z).permCongr.symm
        (pi.subtypePermOfFintype htail) i)
    rw [Equiv.permCongr_symm_apply, Equiv.apply_symm_apply]
  exact congrArg Subtype.val hsubtype

private lemma suffix_avoids312 {n : Nat} [NeZero n]
    {pi : Equiv.Perm (Fin n)} {z : Fin n}
    (hz : pi z = 0) (h312 : Avoids312 pi) :
    Avoids312 (suffixPerm pi z (fun _x hx => suffix_maps_suffix hz h312 hx)) := by
  intro hcontains
  let htail : ∀ x, z < x → z < pi x := fun x hx => suffix_maps_suffix hz h312 hx
  let rho := suffixPerm pi z htail
  change Contains pattern312 rho at hcontains
  rcases (contains312_iff rho).mp hcontains with ⟨a, b, c, hab, hbc, hbcv, hcav⟩
  apply h312
  apply (contains312_iff pi).mpr
  refine ⟨(tailEquiv z a).val, (tailEquiv z b).val, (tailEquiv z c).val,
    tailEquiv_strictMono z hab, tailEquiv_strictMono z hbc, ?_, ?_⟩
  · rw [suffixPerm_apply pi z htail, suffixPerm_apply pi z htail]
    exact tailEquiv_strictMono z hbcv
  · rw [suffixPerm_apply pi z htail, suffixPerm_apply pi z htail]
    exact tailEquiv_strictMono z hcav

private lemma suffix_avoids321 {n : Nat} [NeZero n]
    {pi : Equiv.Perm (Fin n)} {z : Fin n}
    (hz : pi z = 0) (h312 : Avoids312 pi) (h321 : Avoids321 pi) :
    Avoids321 (suffixPerm pi z (fun _x hx => suffix_maps_suffix hz h312 hx)) := by
  intro hcontains
  let htail : ∀ x, z < x → z < pi x := fun x hx => suffix_maps_suffix hz h312 hx
  let rho := suffixPerm pi z htail
  change Contains pattern321 rho at hcontains
  rcases (contains321_iff rho).mp hcontains with ⟨a, b, c, hab, hbc, hcbv, hbav⟩
  apply h321
  apply (contains321_iff pi).mpr
  refine ⟨(tailEquiv z a).val, (tailEquiv z b).val, (tailEquiv z c).val,
    tailEquiv_strictMono z hab, tailEquiv_strictMono z hbc, ?_, ?_⟩
  · rw [suffixPerm_apply pi z htail, suffixPerm_apply pi z htail]
    exact tailEquiv_strictMono z hcbv
  · rw [suffixPerm_apply pi z htail, suffixPerm_apply pi z htail]
    exact tailEquiv_strictMono z hbav

private theorem exists_rotationSumComposition_of_avoids :
    ∀ {n : Nat} (pi : Equiv.Perm (Fin n)),
      Avoids312 pi → Avoids321 pi →
        ∃ c : Composition n, pi = rotationSumComposition c := by
  intro n pi h312 h321
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        exact ⟨Composition.ones 0, Subsingleton.elim _ _⟩
      · let : NeZero n := ⟨hn⟩
        let z : Fin n := pi.symm 0
        have hz : pi z = 0 := pi.apply_symm_apply 0
        let r := z.val + 1
        let m := n - r
        have hr_pos : 0 < r := by simp [r]
        have hr_le : r ≤ n := by
          dsimp [r]
          omega
        have hm_lt : m < n := by
          dsimp [m]
          omega
        let htail : ∀ x, z < x → z < pi x :=
          fun x hx => suffix_maps_suffix hz h312 hx
        let rho : Equiv.Perm (Fin m) := suffixPerm pi z htail
        have hrho312 : Avoids312 rho := by
          exact suffix_avoids312 hz h312
        have hrho321 : Avoids321 rho := by
          exact suffix_avoids321 hz h312 h321
        obtain ⟨c, hc⟩ := ih m hm_lt rho hrho312 hrho321
        have hsum : r + m = n := by
          dsimp [m]
          omega
        let d : Composition n :=
          (Composition.append (Composition.single r hr_pos) c).cast hsum
        refine ⟨d, ?_⟩
        ext x
        by_cases hx : x ≤ z
        · let i0 : Fin d.length := ⟨0, by
            exact Composition.length_pos_of_pos d (Nat.pos_of_ne_zero hn)⟩
          have hx_lt_r : x.val < r := by
            dsimp [r]
            exact Nat.lt_succ_iff.mpr hx
          let j : Fin (d.blocksFun i0) := ⟨x.val, by
            simpa [d, i0, Composition.blocksFun, Composition.cast,
              Composition.append, Composition.single] using hx_lt_r⟩
          let p : Sigma fun i : Fin d.length => Fin (d.blocksFun i) := ⟨i0, j⟩
          have hpx : d.blocksFinEquiv p = x := by
            apply Fin.ext
            rw [blocksFinEquiv_val]
            simp [d, p, i0, j,
              Composition.sizeUpTo, Composition.cast, Composition.append,
              Composition.single]
          have hsize0 : d.sizeUpTo i0.val = 0 := by
            simp [d, i0, Composition.sizeUpTo, Composition.cast,
              Composition.append, Composition.single]
          have hblock0 : d.blocksFun i0 = r := by
            rfl
          have hrotate0 :
              (finRotate (d.blocksFun i0) j).val = (x.val + 1) % r := by
            rw [finRotate_apply]
            simp [Fin.add_def, j, hblock0]
          have hrot := rotationSumComposition_apply_blocksFinEquiv d p
          calc
            (pi x).val =
                (d.blocksFinEquiv
                  ⟨p.1, finRotate (d.blocksFun p.1) p.2⟩).val := by
              rw [blocksFinEquiv_val]
              change (pi x).val = d.sizeUpTo i0.val +
                (finRotate (d.blocksFun i0) j).val
              rw [hsize0, zero_add, hrotate0]
              by_cases hxz : x = z
              · rw [hxz, hz]
                simp [r]
              · have hxz_lt : x < z := lt_of_le_of_ne hx hxz
                have hpref := prefix_apply hz h312 h321 hxz_lt
                rw [Nat.mod_eq_of_lt]
                · exact hpref
                · dsimp [r]
                  omega
            _ = (rotationSumComposition d (d.blocksFinEquiv p)).val :=
              congrArg Fin.val hrot.symm
            _ = (rotationSumComposition d x).val := by rw [hpx]
        · have hxz : z < x := lt_of_not_ge hx
          let y : Fin m := (tailEquiv z).symm ⟨x, hxz⟩
          let q : Sigma fun i : Fin c.length => Fin (c.blocksFun i) :=
            c.blocksFinEquiv.symm y
          have hdlen : d.length = c.length + 1 := by
            change (r :: c.blocks).length = c.blocks.length + 1
            simp
          let iq : Fin d.length := ⟨q.1.val + 1, by
            rw [hdlen]
            omega⟩
          let jq : Fin (d.blocksFun iq) := ⟨q.2.val, by
            simp_all [d, iq, q, Composition.blocksFun, Composition.cast,
              Composition.append, Composition.single]⟩
          let p : Sigma fun i : Fin d.length => Fin (d.blocksFun i) := ⟨iq, jq⟩
          have hsize_iq : d.sizeUpTo iq.val = r + c.sizeUpTo q.1.val := by
            simp [d, iq, q, Composition.sizeUpTo, Composition.cast,
              Composition.append, Composition.single]
          have hblock_iq : d.blocksFun iq = c.blocksFun q.1 := by
            simp [d, iq, q, Composition.blocksFun, Composition.cast,
              Composition.append, Composition.single]
          have hrotate_iq :
              (finRotate (d.blocksFun iq) jq).val =
                (finRotate (c.blocksFun q.1) q.2).val := by
            simp only [finRotate_apply]
            simp [Fin.add_def, jq, hblock_iq]
          have hqy : c.blocksFinEquiv q = y := c.blocksFinEquiv.apply_symm_apply y
          have hpx : d.blocksFinEquiv p = x := by
            apply Fin.ext
            have hqy_val := congrArg Fin.val hqy
            rw [blocksFinEquiv_val]
            rw [blocksFinEquiv_val] at hqy_val
            change d.sizeUpTo iq.val + jq.val = x.val
            rw [hsize_iq]
            have hy_val : y.val = x.val - r := by
              rfl
            have hjq : jq.val = q.2.val := rfl
            rw [hjq, Nat.add_assoc, hqy_val, hy_val]
            dsimp [r] at hxz ⊢
            omega
          have hc_apply : rho y = rotationSumComposition c y :=
            congrArg (fun e : Equiv.Perm (Fin m) => e y) hc
          have hrho := suffixPerm_apply pi z htail y
          have hyx : (tailEquiv z y).val = x :=
            congrArg Subtype.val ((tailEquiv z).apply_symm_apply ⟨x, hxz⟩)
          have hpi_tail :
              pi x = (tailEquiv z (rotationSumComposition c y)).val := by
            rw [← hyx, ← hc_apply]
            exact hrho
          have hrot := rotationSumComposition_apply_blocksFinEquiv c q
          have hblock_tail :
              c.blocksFinEquiv ⟨q.1, finRotate (c.blocksFun q.1) q.2⟩ =
                rotationSumComposition c y := by
            rw [← hrot, hqy]
          have hrot_global := rotationSumComposition_apply_blocksFinEquiv d p
          calc
            (pi x).val = (tailEquiv z (rotationSumComposition c y)).val.val :=
              congrArg Fin.val hpi_tail
            _ = (d.blocksFinEquiv
                  ⟨p.1, finRotate (d.blocksFun p.1) p.2⟩).val := by
              rw [blocksFinEquiv_val]
              have hblock_tail_val := congrArg Fin.val hblock_tail
              rw [blocksFinEquiv_val] at hblock_tail_val
              change (tailEquiv z (rotationSumComposition c y)).val.val =
                d.sizeUpTo iq.val + (finRotate (d.blocksFun iq) jq).val
              rw [hsize_iq, hrotate_iq]
              dsimp [tailEquiv, r]
              simpa [Nat.add_assoc] using
                congrArg (fun v => z.val + 1 + v) hblock_tail_val.symm
            _ = (rotationSumComposition d (d.blocksFinEquiv p)).val :=
              congrArg Fin.val hrot_global.symm
            _ = (rotationSumComposition d x).val := by rw [hpx]

private lemma finRotate_le_iff_last {m : Nat} (j : Fin m) :
    (finRotate m j).val ≤ j.val ↔ j.val + 1 = m := by
  have hval : (finRotate m j).val = (j.val + 1) % m := by
    have := congrArg Fin.val (finRotate_apply j)
    simp [Fin.add_def] at this ⊢
  have hjle : j.val + 1 ≤ m := Nat.succ_le_iff.mpr j.isLt
  rw [hval]
  constructor
  · intro h
    by_contra hne
    have hlt : j.val + 1 < m := lt_of_le_of_ne hjle hne
    rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · intro heq
    rw [heq, Nat.mod_self]
    exact Nat.zero_le _

private lemma rotationSumComposition_le_iff_last {n : Nat} (c : Composition n)
    (p : Sigma fun i : Fin c.length => Fin (c.blocksFun i)) :
    rotationSumComposition c (c.blocksFinEquiv p) ≤ c.blocksFinEquiv p ↔
      p.2.val + 1 = c.blocksFun p.1 := by
  rw [rotationSumComposition_apply_blocksFinEquiv]
  rw [Fin.le_iff_val_le_val, blocksFinEquiv_val, blocksFinEquiv_val]
  change c.sizeUpTo p.1.val + (finRotate (c.blocksFun p.1) p.2).val ≤
      c.sizeUpTo p.1.val + p.2.val ↔ _
  rw [Nat.add_le_add_iff_left, finRotate_le_iff_last]

private lemma mem_boundaries_iff_zero_or_rotation_le {n : Nat} (c : Composition n)
    (j : Fin (n + 1)) :
    j ∈ c.boundaries ↔
      j = 0 ∨ ∃ x : Fin n, x.val + 1 = j.val ∧ rotationSumComposition c x ≤ x := by
  constructor
  · intro hj
    rcases c.toCompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq.mp hj with
      ⟨i, hi, hsum⟩
    rw [c.toCompositionAsSet.card_boundaries_eq_succ_length,
      c.toCompositionAsSet_length] at hi
    cases i with
    | zero =>
        left
        apply Fin.ext
        simpa using hsum.symm
    | succ k =>
        right
        have hk : k < c.length := by omega
        let bi : Fin c.length := ⟨k, hk⟩
        have hbpos : 0 < c.blocksFun bi := c.one_le_blocksFun bi
        let last : Fin (c.blocksFun bi) := ⟨c.blocksFun bi - 1, by omega⟩
        let p : Sigma fun i : Fin c.length => Fin (c.blocksFun i) := ⟨bi, last⟩
        let x : Fin n := c.blocksFinEquiv p
        refine ⟨x, ?_, ?_⟩
        · have hstep := c.sizeUpTo_succ hk
          change c.sizeUpTo (k + 1) = c.sizeUpTo k + c.blocksFun bi at hstep
          have hxval :
              x.val = c.sizeUpTo k + (c.blocksFun bi - 1) := by
            dsimp [x]
            rw [blocksFinEquiv_val]
          rw [Composition.toCompositionAsSet_blocks] at hsum
          change c.sizeUpTo (k + 1) = j.val at hsum
          omega
        · exact (rotationSumComposition_le_iff_last c p).mpr (by
            dsimp [p, last]
            omega)
  · rintro (rfl | ⟨x, hxj, hfall⟩)
    · exact c.toCompositionAsSet.zero_mem
    · let p : Sigma fun i : Fin c.length => Fin (c.blocksFun i) :=
        c.blocksFinEquiv.symm x
      have hpx : c.blocksFinEquiv p = x := c.blocksFinEquiv.apply_symm_apply x
      have hfallp :
          rotationSumComposition c (c.blocksFinEquiv p) ≤ c.blocksFinEquiv p := by
        simpa [hpx] using hfall
      have hlast := (rotationSumComposition_le_iff_last c p).mp hfallp
      apply c.toCompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq.mpr
      refine ⟨p.1.val + 1, ?_, ?_⟩
      · rw [c.toCompositionAsSet.card_boundaries_eq_succ_length,
          c.toCompositionAsSet_length]
        omega
      · have hstep := c.sizeUpTo_succ p.1.isLt
        change c.sizeUpTo (p.1.val + 1) =
          c.sizeUpTo p.1.val + c.blocksFun p.1 at hstep
        have hpxval := congrArg Fin.val hpx
        rw [blocksFinEquiv_val] at hpxval
        rw [Composition.toCompositionAsSet_blocks]
        change c.sizeUpTo (p.1.val + 1) = j.val
        omega

/-- A permutation avoids `312` and `321` exactly when it is the rotation sum of a composition. -/
theorem avoids_312_321_iff_exists_rotationSumComposition {n : Nat}
    (pi : Equiv.Perm (Fin n)) :
    Avoids312 pi ∧ Avoids321 pi ↔
      ∃ c : Composition n, pi = rotationSumComposition c := by
  constructor
  · rintro ⟨h312, h321⟩
    exact exists_rotationSumComposition_of_avoids pi h312 h321
  · rintro ⟨c, rfl⟩
    exact rotationSumComposition_avoids_312_321 c

/-- Distinct compositions give distinct direct sums of cyclic rotations. -/
theorem rotationSumComposition_injective {n : Nat} :
    Function.Injective (@rotationSumComposition n) := by
  intro c₁ c₂ hperm
  apply (compositionEquiv n).injective
  apply CompositionAsSet.ext
  ext j
  change j ∈ c₁.boundaries ↔ j ∈ c₂.boundaries
  rw [mem_boundaries_iff_zero_or_rotation_le,
    mem_boundaries_iff_zero_or_rotation_le]
  constructor
  · rintro (hj | ⟨x, hxj, hx⟩)
    · exact Or.inl hj
    · exact Or.inr ⟨x, hxj, by simpa [hperm] using hx⟩
  · rintro (hj | ⟨x, hxj, hx⟩)
    · exact Or.inl hj
    · exact Or.inr ⟨x, hxj, by simpa [hperm] using hx⟩

private lemma contains2143_finCongr_permCongr_iff {m n : Nat} (h : m = n)
    (pi : Equiv.Perm (Fin m)) :
    Contains2143 (⇑((finCongr h).permCongr pi)) ↔ Contains2143 (⇑pi) := by
  subst n
  have hpi : (finCongr rfl).permCongr pi = pi := by
    ext x
    rfl
  rw [hpi]

private lemma rotationSumComposition_cube_contains2143_iff {n : Nat}
    (c : Composition n) :
    Contains2143 (⇑(rotationSumComposition c ^ 3)) ↔
      Contains2143 (⇑(rotationSumPerm c.blocks ^ 3)) := by
  have hpow := map_pow (finCongr (composition_index_sum c)).permCongrHom
    (rotationSumPerm c.blocks) 3
  have hpow' :
      (finCongr (composition_index_sum c)).permCongr (rotationSumPerm c.blocks ^ 3) =
        ((finCongr (composition_index_sum c)).permCongr
          (rotationSumPerm c.blocks)) ^ 3 := by
    simpa only [Equiv.permCongrHom_coe] using hpow
  rw [rotationSumComposition, ← hpow']
  exact contains2143_finCongr_permCongr_iff (composition_index_sum c) _

/-- The cube of a composition's rotation sum avoids `2143` exactly under the 6.221 block bound. -/
theorem rotationSumComposition_cube_avoids_2143_iff {n : Nat} (c : Composition n) :
    (¬Contains2143 (⇑(rotationSumComposition c ^ 3))) ↔
      (Finset.univ.filter fun i : Fin c.length =>
        c.blocksFun i ≠ 1 ∧ c.blocksFun i ≠ 3).card ≤ 1 := by
  rw [rotationSumComposition_cube_contains2143_iff]
  have hpos : ∀ i : Fin c.blocks.length, 0 < c.blocks.get i :=
    fun i => c.blocks_pos (List.get_mem c.blocks i)
  change (¬Contains2143 (⇑(rotationSumPerm c.blocks ^ 3))) ↔
    (Finset.univ.filter fun i : Fin c.blocks.length =>
      c.blocks.get i ≠ 1 ∧ c.blocks.get i ≠ 3).card ≤ 1
  exact rotationSumPerm_cube_avoids_2143_iff hpos

open Classical in
/-- The 6.222 count: constrained pattern avoiders are counted by constrained compositions. -/
theorem card_avoids_312_321_cube_2143_eq_compositions (n : Nat) :
    (Finset.univ.filter fun pi : Equiv.Perm (Fin n) =>
      Avoids312 pi ∧ Avoids321 pi ∧
        ¬Contains2143 (⇑(pi ^ 3))).card =
      (Finset.univ.filter fun c : Composition n =>
        (Finset.univ.filter fun i : Fin c.length =>
          c.blocksFun i ≠ 1 ∧ c.blocksFun i ≠ 3).card ≤ 1).card := by
  classical
  symm
  apply Finset.card_bij (fun c _ => rotationSumComposition c)
  · intro c hc
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · exact (rotationSumComposition_avoids_312_321 c).1
    · exact (rotationSumComposition_avoids_312_321 c).2
    · exact (rotationSumComposition_cube_avoids_2143_iff c).mpr hc.2
  · intro c₁ _hc₁ c₂ _hc₂ heq
    exact rotationSumComposition_injective heq
  · intro pi hpi
    rw [Finset.mem_filter] at hpi
    obtain ⟨c, hc⟩ :=
      (avoids_312_321_iff_exists_rotationSumComposition pi).mp ⟨hpi.2.1, hpi.2.2.1⟩
    refine ⟨c, ?_, hc.symm⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (rotationSumComposition_cube_avoids_2143_iff c).mp
    simpa [← hc] using hpi.2.2.2

example :
    Avoids312 (rotationSumComposition (Composition.single 1 Nat.zero_lt_one)) ∧
      Avoids321 (rotationSumComposition (Composition.single 1 Nat.zero_lt_one)) := by
  exact rotationSumComposition_avoids_312_321 _

example : ∃ c : Composition 1, ¬Contains2143 (⇑(rotationSumComposition c ^ 3)) := by
  refine ⟨Composition.single 1 Nat.zero_lt_one, ?_⟩
  apply (rotationSumComposition_cube_avoids_2143_iff _).mpr
  decide

end D5.S3.ConceptDynamics.PatternAvoidance.ArcherBourneDecomposition
