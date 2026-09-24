/- GID: D5/S1/Words/Patterns/A398542MinimumRecurrence
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/A398542MinimumRecurrence
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Minimum splitting and interval cardinalities of actual fixed-bottom permutations. -/

import D5.S1.Words.Patterns.A398542FixedBottom
import D5.S1.Words.Patterns.Separable.CutFactorization

namespace D5.S1.Words.Patterns.A398542MinimumRecurrence

open D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)
open D5.S1.Words.Patterns.A398542FixedBottom
open D5.S1.Words.Patterns.Separable.CutFactorization (blockSum)

noncomputable section

/-- The interval condition on the gaps of an actual source permutation. -/
def IntervalActual {m : ℕ} (b : Equiv.Perm (Fin m)) (l h k : ℕ) :=
  {w : Actual b k // ∀ i, l ≤ (gap (extractShuffle w.val) i).val ∧
    (gap (extractShuffle w.val) i).val ≤ h}

/-- Restriction of the existing configuration class, with the same entire bottom. -/
def IntervalConfiguration {m : ℕ} (b : Equiv.Perm (Fin m)) (l h k : ℕ) :=
  {w : Configuration b k // ∀ i, l ≤ (w.val.2.val i).val ∧ (w.val.2.val i).val ≤ h}

/-- Literal cardinality; this definition makes no recursive counting assumption. -/
def intervalCount {m : ℕ} (b : Equiv.Perm (Fin m)) (l h k : ℕ) : ℕ :=
  Nat.card (IntervalActual b l h k)

/-- The forced upper values: left shifted by `c+1`, root zero, right shifted by one. -/
def joinUpper {a c : ℕ} (v : Equiv.Perm (Fin a)) (r : Equiv.Perm (Fin c)) :
    Equiv.Perm (Fin (a + (c + 1))) :=
  blockSum true v ((finSuccEquiv c).trans ((Equiv.optionCongr r).trans (finSuccEquiv c).symm))

/-- A minimum join avoids 213 exactly when both children do, including empty children. -/
theorem join_avoids_iff {a c : ℕ} (v : Equiv.Perm (Fin a)) (r : Equiv.Perm (Fin c)) :
    ¬Contains pattern213 (joinUpper v r) ↔
      ¬Contains pattern213 v ∧ ¬Contains pattern213 r := by
  let u := joinUpper v r
  have vl (i : Fin a) : (u (i.castAdd (c + 1))).val = c + 1 + (v i).val := by
    simp [u, joinUpper, blockSum, Equiv.sumComm, Nat.add_comm]
  have vz : u (Fin.natAdd a 0) = 0 := by
    apply Fin.ext
    simp [u, joinUpper, blockSum, Equiv.sumComm]
  have vr (i : Fin c) : (u (Fin.natAdd a i.succ)).val = (r i).val + 1 := by
    simp [u, joinUpper, blockSum, Equiv.sumComm]
  have lift (n : ℕ) (p : Equiv.Perm (Fin n)) (e : Fin n ↪o Fin (a + (c + 1)))
      (he : ∀ i j, p i < p j ↔ u (e i) < u (e j)) :
      Contains pattern213 p → Contains pattern213 u := by
    rintro ⟨f, hf⟩
    exact ⟨f.trans e, fun i j => (hf i j).trans (he _ _)⟩
  constructor
  · intro hu
    constructor
    · apply mt (lift a v (OrderEmbedding.ofStrictMono (Fin.castAdd (c + 1))
        (by intro i j hij; exact hij)) ?_) hu
      intro i j
      change v i < v j ↔ u (i.castAdd (c + 1)) < u (j.castAdd (c + 1))
      simp only [Fin.lt_def, vl, Nat.add_lt_add_iff_left]
    · apply mt (lift c r (OrderEmbedding.ofStrictMono (fun i => Fin.natAdd a i.succ)
        (by intro i j hij; simpa using hij)) ?_) hu
      intro i j
      change r i < r j ↔ u (Fin.natAdd a i.succ) < u (Fin.natAdd a j.succ)
      simp only [Fin.lt_def, vr, Nat.add_lt_add_iff_right]
  · rintro ⟨hv, hr⟩ ⟨f, hf⟩
    have p01 : f 0 < f 1 := f.strictMono (by decide)
    have p12 : f 1 < f 2 := f.strictMono (by decide)
    have q10 : u (f 1) < u (f 0) := (hf 1 0).mp (by decide)
    have q02 : u (f 0) < u (f 2) := (hf 0 2).mp (by decide)
    have left (i : Fin (a + (c + 1))) (hi : i.val < a) :
        (u i).val = c + 1 + (v ⟨i.val, hi⟩).val := vl ⟨i.val, hi⟩
    have right (i : Fin (a + (c + 1))) (hi : a < i.val) :
        (u i).val = (r ⟨i.val - a - 1, by have := i.isLt; omega⟩).val + 1 := by
      have ei : i = Fin.natAdd a (⟨i.val - a - 1, by have := i.isLt; omega⟩ : Fin c).succ := by
        apply Fin.ext; simp; omega
      exact (congrArg (fun x => (u x).val) ei).trans (vr _)
    have zero (i : Fin (a + (c + 1))) (hi : i.val = a) : u i = 0 := by
      have ei : i = Fin.natAdd a 0 := Fin.ext (by simpa using hi)
      rw [ei, vz]
    have sides : (∀ i, (f i).val < a) ∨ (∀ i, a < (f i).val) := by
      by_cases h2 : (f 2).val < a
      · left; intro i; fin_cases i <;> dsimp <;> omega
      by_cases h0 : a < (f 0).val
      · right; intro i; fin_cases i <;> dsimp <;> omega
      by_cases h0z : (f 0).val = a
      · rw [zero _ h0z] at q10; exact (Fin.not_lt_zero _ q10).elim
      have h0l : (f 0).val < a := by omega
      by_cases h2z : (f 2).val = a
      · rw [zero _ h2z] at q02; exact (Fin.not_lt_zero _ q02).elim
      have h2r : a < (f 2).val := by omega
      have e0 := left _ h0l
      have e2 := right _ h2r
      have hb := (r ⟨(f 2).val - a - 1, by have := (f 2).isLt; omega⟩).isLt
      omega
    rcases sides with hl | hh
    · apply hv
      let e : Fin 3 ↪o Fin a := OrderEmbedding.ofStrictMono
        (fun i => ⟨(f i).val, hl i⟩) (by intro i j hij; exact f.strictMono hij)
      refine ⟨e, fun i j => ?_⟩
      rw [hf]
      change (u (f i)).val < (u (f j)).val ↔ _
      rw [left _ (hl i), left _ (hl j)]
      exact Nat.add_lt_add_iff_left
    · apply hr
      let e : Fin 3 ↪o Fin c := OrderEmbedding.ofStrictMono
        (fun i => ⟨(f i).val - a - 1, by have := (f i).isLt; have := hh i; omega⟩)
        (by intro i j hij; have := f.strictMono hij; have := hh i; have := hh j
            change (f i).val - a - 1 < (f j).val - a - 1; omega)
      refine ⟨e, fun i j => ?_⟩
      rw [hf]
      change (u (f i)).val < (u (f j)).val ↔ _
      rw [right _ (hh i), right _ (hh j)]
      exact Nat.add_lt_add_iff_right

/-- Splitting at the actual minimum forces both value sets, hence unique standardized
children. Their sizes may be zero; there is no choice of a subset of upper values. -/
theorem minimum_factorization {a c : ℕ} (u : Equiv.Perm (Fin (a + (c + 1))))
    (hz : u (Fin.natAdd a 0) = 0) (hu : ¬Contains pattern213 u) :
    ∃! q : Equiv.Perm (Fin a) × Equiv.Perm (Fin c),
      joinUpper q.1 q.2 = u ∧ ¬Contains pattern213 q.1 ∧ ¬Contains pattern213 q.2 := by
  classical
  have nz (i : Fin (a + (c + 1))) (hi : i ≠ Fin.natAdd a 0) : 0 < u i := by
    apply Fin.pos_iff_ne_zero.mpr
    intro he
    exact hi (u.injective (he.trans hz.symm))
  have cross (i : Fin a) (j : Fin c) :
      u (Fin.natAdd a j.succ) < u (i.castAdd (c + 1)) := by
    have hn : u (i.castAdd (c + 1)) ≠ u (Fin.natAdd a j.succ) := by
      intro he
      have := congrArg Fin.val (u.injective he)
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_succ] at this
      omega
    by_contra hh
    have hv := lt_of_le_of_ne (le_of_not_gt hh) hn
    have hmin := nz (i.castAdd (c + 1)) (by
      intro he; have := congrArg Fin.val he; simp at this; omega)
    apply hu
    refine ⟨OrderEmbedding.ofStrictMono
      ![i.castAdd (c + 1), Fin.natAdd a 0, Fin.natAdd a j.succ] ?_, ?_⟩
    · intro s t hst
      fin_cases s <;> fin_cases t <;>
        simp_all only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          Fin.reduceFinMk, Matrix.cons_val, Fin.lt_def, Fin.val_castAdd,
          Fin.val_natAdd, Fin.val_succ, Fin.val_zero] <;> omega
    · intro s t
      change pattern213 s < pattern213 t ↔
        u (![i.castAdd (c + 1), Fin.natAdd a 0, Fin.natAdd a j.succ] s) <
        u (![i.castAdd (c + 1), Fin.natAdd a 0, Fin.natAdd a j.succ] t)
      fin_cases s <;> fin_cases t <;> simp [pattern213, hz] <;> omega
  let lv : Fin a → Fin (a + (c + 1)) := fun i => u (i.castAdd (c + 1))
  let rv : Fin c → Fin (a + (c + 1)) := fun i => u (Fin.natAdd a i.succ)
  let v := (Tuple.sort lv).symm
  let r := (Tuple.sort rv).symm
  have lm : StrictMono (lv ∘ Tuple.sort lv) :=
    (Tuple.monotone_sort lv).strictMono_of_injective
      ((u.injective.comp (Fin.castAdd_injective a (c + 1))).comp (Tuple.sort lv).injective)
  have rm : StrictMono (rv ∘ Tuple.sort rv) :=
    (Tuple.monotone_sort rv).strictMono_of_injective
      ((u.injective.comp ((Fin.natAdd_injective (c + 1) a).comp (Fin.succ_injective c))).comp
        (Tuple.sort rv).injective)
  have leq (i j : Fin a) : v i < v j ↔ lv i < lv j := by
    simpa [v, Function.comp_def] using (lm.lt_iff_lt (a := v i) (b := v j)).symm
  have req (i j : Fin c) : r i < r j ↔ rv i < rv j := by
    simpa [r, Function.comp_def] using (rm.lt_iff_lt (a := r i) (b := r j)).symm
  have jl (v : Equiv.Perm (Fin a)) (r : Equiv.Perm (Fin c)) (i : Fin a) :
      (joinUpper v r (i.castAdd (c + 1))).val = c + 1 + (v i).val := by
    simp [joinUpper, blockSum, Equiv.sumComm, Nat.add_comm]
  have jz (v : Equiv.Perm (Fin a)) (r : Equiv.Perm (Fin c)) :
      joinUpper v r (Fin.natAdd a 0) = 0 := by
    apply Fin.ext; simp [joinUpper, blockSum, Equiv.sumComm]
  have jr (v : Equiv.Perm (Fin a)) (r : Equiv.Perm (Fin c)) (i : Fin c) :
      (joinUpper v r (Fin.natAdd a i.succ)).val = (r i).val + 1 := by
    simp [joinUpper, blockSum, Equiv.sumComm]
  have same (i j : Fin (a + (c + 1))) :
      joinUpper v r i < joinUpper v r j ↔ u i < u j := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · change _ ↔ lv i < lv j
      rw [← leq]
      simp only [Fin.lt_def, jl, Nat.add_lt_add_iff_left]
    · refine Fin.cases ?_ (fun j => ?_) j
      · rw [jz, hz]; simp
      · have := cross i j
        simp only [Fin.lt_def, jl, jr]
        have := (r j).isLt
        omega
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [jz, hz]
        have hn := nz (j.castAdd (c + 1)) (by
          intro he; have := congrArg Fin.val he; simp at this; omega)
        simp only [Fin.lt_def, jl, Fin.val_zero] at *
        omega
      · have := cross j i
        simp only [Fin.lt_def, jl, jr]
        have := (r i).isLt
        omega
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · rw [jz, hz]
      · rw [jz, hz]
        have hn := nz (Fin.natAdd a j.succ) (by
          intro he; have := congrArg Fin.val he; simp at this)
        simp only [Fin.lt_def, jr, Fin.val_zero] at *
        omega
      · rw [jz, hz]; simp
      · change _ ↔ rv i < rv j
        rw [← req]
        simp only [Fin.lt_def, jr, Nat.add_lt_add_iff_right]
  have he : joinUpper v r = u := by
    have mono : StrictMono ((joinUpper v r).symm.trans u) := by
      intro i j hij
      apply (same _ _).mp
      simpa using hij
    have hid := (Equiv.Perm.monotone_iff _).mp mono.monotone
    apply Equiv.ext
    intro i
    have hh := Equiv.congr_fun hid (joinUpper v r i)
    simpa using hh.symm
  refine ⟨(v, r), ⟨he, (join_avoids_iff v r).mp (he.symm ▸ hu)⟩, ?_⟩
  rintro ⟨v', r'⟩ ⟨he', _⟩
  apply Prod.ext
  · apply Equiv.ext; intro i; apply Fin.ext
    change (v' i).val = (v i).val
    have hh := congrArg (fun p : Equiv.Perm (Fin (a + (c + 1))) =>
      (p (i.castAdd (c + 1))).val) (he'.trans he.symm)
    simp only [jl] at hh
    omega
  · apply Equiv.ext; intro i; apply Fin.ext
    change (r' i).val = (r i).val
    have hh := congrArg (fun p : Equiv.Perm (Fin (a + (c + 1))) =>
      (p (Fin.natAdd a i.succ)).val) (he'.trans he.symm)
    simp only [jr] at hh
    omega

/-- In-order concatenation retains repeated gaps at either side of the root. -/
def joinGaps {m a c : ℕ} (g : Fin (m + 1)) (v : Fin a → Fin (m + 1))
    (r : Fin c → Fin (m + 1)) : Fin (a + (c + 1)) → Fin (m + 1) :=
  Fin.addCases v (Fin.cases g r)

/-- Reconstruct one valid configuration on one entire bottom. The right deadline
is imposed only at this root; no monotonicity of `dead` is used. -/
def joinConfiguration {m a c l h : ℕ} (b : Equiv.Perm (Fin m))
    (g : Fin (m + 1)) (hl : l ≤ g.val) (hh : g.val ≤ h) (hd : g.val < dead b g.val)
    (v : IntervalConfiguration b l g.val a)
    (r : IntervalConfiguration b g.val (min h (dead b g.val - 1)) c) :
    IntervalConfiguration b l h (a + (c + 1)) := by
  have rightInterval : g.val ≤ min h (dead b g.val - 1) := le_min hh (by omega)
  let u := joinUpper v.val.val.1 r.val.val.1
  let γ := joinGaps g v.val.val.2.val r.val.val.2.val
  have gl (i : Fin a) : γ (i.castAdd (c + 1)) = v.val.val.2.val i := by simp [γ, joinGaps]
  have gz : γ (Fin.natAdd a 0) = g := by simp [γ, joinGaps]
  have gr (i : Fin c) : γ (Fin.natAdd a i.succ) = r.val.val.2.val i := by simp [γ, joinGaps]
  have vl (i : Fin a) : (u (i.castAdd (c + 1))).val = c + 1 + (v.val.val.1 i).val := by
    simp [u, joinUpper, blockSum, Equiv.sumComm, Nat.add_comm]
  have vz : u (Fin.natAdd a 0) = 0 := by
    apply Fin.ext; simp [u, joinUpper, blockSum, Equiv.sumComm]
  have vr (i : Fin c) : (u (Fin.natAdd a i.succ)).val = (r.val.val.1 i).val + 1 := by
    simp [u, joinUpper, blockSum, Equiv.sumComm]
  have hm : Monotone γ := by
    intro i j hij
    revert hij
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro hij
      rw [gl, gl]
      exact v.val.val.2.property hij
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _; rw [gl, gz]; exact (v.property i).2
      · intro _; rw [gl, gr]
        exact le_trans (v.property i).2 (r.property j).1
    · intro hij
      have := i.isLt; have := j.isLt
      simp only [Fin.le_def, Fin.val_castAdd, Fin.val_natAdd] at hij
      omega
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro _; rfl
      · intro _; rw [gz, gr]; exact (r.property j).1
      · intro hij; simp at hij
      · intro hij; rw [gr, gr]
        exact r.val.val.2.property (by simpa using hij)
  refine ⟨⟨(u, ⟨γ, hm⟩), (join_avoids_iff _ _).mpr
    ⟨v.val.property.1, r.val.property.1⟩, ?_⟩, ?_⟩
  · intro i j hij huv
    change (γ j).val < dead b (γ i).val
    revert hij huv
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro hij huv
      rw [gl, gl]
      exact v.val.property.2 i j hij (by
        change (u _).val < (u _).val at huv
        rw [vl, vl] at huv; omega)
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _ huv; rw [vz] at huv; exact (Fin.not_lt_zero _ huv).elim
      · intro _ huv
        change (u _).val < (u _).val at huv
        rw [vl, vr] at huv
        have := (r.val.val.1 j).isLt
        omega
    · intro hij _
      simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hij
      have := j.isLt; omega
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hij _; exact (lt_irrefl _ hij).elim
      · intro _ _; rw [gz, gr]
        have := (r.property j).2
        omega
      · intro hij _; simp at hij
      · intro hij huv
        rw [gr, gr]
        exact r.val.property.2 i j (by simpa using hij) (by
          change (u _).val < (u _).val at huv
          rw [vr, vr] at huv; omega)
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · change l ≤ (γ _).val ∧ (γ _).val ≤ h
      rw [gl]
      exact ⟨(v.property i).1, le_trans (v.property i).2 hh⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · change l ≤ (γ _).val ∧ (γ _).val ≤ h
        rw [gz]; exact ⟨hl, le_trans rightInterval (min_le_left _ _)⟩
      · change l ≤ (γ _).val ∧ (γ _).val ≤ h
        rw [gr]
        exact ⟨le_trans hl (r.property i).1, le_trans (r.property i).2 (min_le_left _ _)⟩

/-- The disjoint splitting data, with both children still actual permutations over `b`. -/
def SplitActual {m : ℕ} (b : Equiv.Perm (Fin m)) (l h k : ℕ) :=
  Σ g : {g : Fin (m + 1) // l ≤ g.val ∧ g.val ≤ h}, Σ a : Fin (k + 1),
    IntervalActual b l g.val.val a.val ×
      IntervalActual b g.val.val (min h (dead b g.val.val - 1)) (k - a.val)

/-- Actual interval objects have a unique empty object and the minimum-split
convolution. The full interval is exactly the original, nonrecursive source count. -/
theorem actual_cardinal_recurrence {m : ℕ} (b : Equiv.Perm (Fin m))
    (hb : ¬Contains pattern132 b) {l h : ℕ} (_hlh : l ≤ h) (_hhm : h ≤ m) :
    intervalCount b l h 0 = 1 ∧
    (∀ k, Nonempty (IntervalActual b l h (k + 1) ≃ SplitActual b l h k) ∧
      intervalCount b l h (k + 1) =
        ∑ g : {g : Fin (m + 1) // l ≤ g.val ∧ g.val ≤ h}, ∑ a : Fin (k + 1),
          intervalCount b l g.val.val a.val *
            intervalCount b g.val.val (min h (dead b g.val.val - 1)) (k - a.val)) ∧
    (∀ k, intervalCount b 0 m k = count b k) := by
  classical
  let ea (l h k : ℕ) : IntervalActual b l h k ≃ IntervalConfiguration b l h k :=
    (actualEquiv b hb k).subtypeEquiv (fun _ => Iff.rfl)
  have dp (g : Fin (m + 1)) : g.val < dead b g.val := by
    let s : Shuffle m 0 := shuffleOfGaps Fin.elim0 (by intro i; exact Fin.elim0 i)
    let w := insert b (Equiv.refl (Fin 0)) s
    have he := (insertionEquiv m 0).symm_apply_apply ((b, Equiv.refl (Fin 0)), s)
    have hl : lowerPerm w = b := congrArg (fun x => x.1.1) he
    have hu : ¬Contains pattern213 (upperPerm w) := by
      rintro ⟨e, _⟩; exact Fin.elim0 (e 0)
    have hd := (gap_criterion w (hl.symm ▸ hb) hu).2.1 g.val (Nat.le_of_lt_succ g.isLt)
    simpa only [hl] using hd
  have (l h k : ℕ) : Finite (IntervalActual b l h k) := by
    unfold IntervalActual Actual
    infer_instance
  have zero : intervalCount b l h 0 = 1 := by
    rw [intervalCount, Nat.card_congr (ea l h 0)]
    apply Nat.card_eq_one_iff_exists.mpr
    let z : IntervalConfiguration b l h 0 :=
      ⟨⟨(Equiv.refl _, ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩),
        (by rintro ⟨f, _⟩; exact Fin.elim0 (f 0)), by intro i; exact Fin.elim0 i⟩,
        by intro i; exact Fin.elim0 i⟩
    refine ⟨z, fun y => ?_⟩
    apply Subtype.ext; apply Subtype.ext
    apply Prod.ext
    · apply Equiv.ext; intro i; exact Fin.elim0 i
    · apply Subtype.ext; funext i; exact Fin.elim0 i
  refine ⟨zero, ?_, ?_⟩
  · intro k
    let C := IntervalConfiguration b l h (k + 1)
    let D := Σ g : {g : Fin (m + 1) // l ≤ g.val ∧ g.val ≤ h}, Σ a : Fin (k + 1),
      IntervalConfiguration b l g.val.val a.val ×
        IntervalConfiguration b g.val.val (min h (dead b g.val.val - 1)) (k - a.val)
    let resize {s t l h : ℕ} (he : s = t) (w : IntervalConfiguration b l h s) :
        IntervalConfiguration b l h t := he ▸ w
    have rp {s t l h : ℕ} (he : s = t) (w : IntervalConfiguration b l h s) (i : Fin s) :
        ((resize he w).val.val.1 (Fin.cast he i)).val = (w.val.val.1 i).val := by
      subst t; rfl
    have rg {s t l h : ℕ} (he : s = t) (w : IntervalConfiguration b l h s) (i : Fin s) :
        (resize he w).val.val.2.val (Fin.cast he i) = w.val.val.2.val i := by
      subst t; rfl
    let sizeEq (a : Fin (k + 1)) : a.val + ((k - a.val) + 1) = k + 1 := by omega
    let lp (a : Fin (k + 1)) (i : Fin a.val) : Fin (k + 1) := ⟨i.val, by omega⟩
    let rp' (a : Fin (k + 1)) (i : Fin (k - a.val)) : Fin (k + 1) :=
      ⟨a.val + (i.val + 1), by omega⟩
    let f : D → C := fun x => resize (sizeEq x.2.1)
      (joinConfiguration b x.1.val x.1.property.1 x.1.property.2 (dp x.1.val) x.2.2.1 x.2.2.2)
    have fs (x : D) :
        (f x).val.val.1 x.2.1 = 0 ∧ (f x).val.val.2.val x.2.1 = x.1.val ∧
        (∀ i : Fin x.2.1.val,
          ((f x).val.val.1 (lp x.2.1 i)).val = k - x.2.1.val + 1 + (x.2.2.1.val.val.1 i).val ∧
          (f x).val.val.2.val (lp x.2.1 i) = x.2.2.1.val.val.2.val i) ∧
        (∀ i : Fin (k - x.2.1.val),
          ((f x).val.val.1 (rp' x.2.1 i)).val = (x.2.2.2.val.val.1 i).val + 1 ∧
          (f x).val.val.2.val (rp' x.2.1 i) = x.2.2.2.val.val.2.val i) := by
      rcases x with ⟨g, a, v, r⟩
      let w := joinConfiguration b g.val g.property.1 g.property.2 (dp g.val) v r
      have ez : Fin.cast (sizeEq a) (Fin.natAdd a.val 0) = a := Fin.ext (by simp)
      have vp (i) := rp (sizeEq a) w i
      have vg (i) := rg (sizeEq a) w i
      change (resize (sizeEq a) w).val.val.1 a = 0 ∧
        (resize (sizeEq a) w).val.val.2.val a = g.val ∧ _
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply Fin.ext
        have hp := vp (Fin.natAdd a.val 0)
        rw [ez] at hp
        exact hp.trans (by
          change (joinUpper v.val.val.1 r.val.val.1 (Fin.natAdd a.val 0)).val = 0
          simp [joinUpper, blockSum, Equiv.sumComm])
      · have hp := vg (Fin.natAdd a.val 0)
        rw [ez] at hp
        exact hp.trans (by
          change joinGaps g.val v.val.val.2.val r.val.val.2.val (Fin.natAdd a.val 0) = g.val
          simp [joinGaps])
      · intro i
        constructor
        · exact (vp (i.castAdd ((k - a.val) + 1))).trans (by
            change (joinUpper v.val.val.1 r.val.val.1 (i.castAdd ((k - a.val) + 1))).val = _
            simp [joinUpper, blockSum, Equiv.sumComm, Nat.add_comm])
        · exact (vg (i.castAdd ((k - a.val) + 1))).trans (by
            change joinGaps g.val v.val.val.2.val r.val.val.2.val (i.castAdd ((k - a.val) + 1)) = _
            simp [joinGaps])
      · intro i
        constructor
        · exact (vp (Fin.natAdd a.val i.succ)).trans (by
            change (joinUpper v.val.val.1 r.val.val.1 (Fin.natAdd a.val i.succ)).val = _
            simp [joinUpper, blockSum, Equiv.sumComm])
        · exact (vg (Fin.natAdd a.val i.succ)).trans (by
            change joinGaps g.val v.val.val.2.val r.val.val.2.val (Fin.natAdd a.val i.succ) = _
            simp [joinGaps])
    have fi : Function.Injective f := by
      intro x y he
      have amin (x : D) : (f x).val.val.1.symm 0 = x.2.1 := by
        apply (f x).val.val.1.injective
        rw [Equiv.apply_symm_apply, (fs x).1]
      have ha : x.2.1 = y.2.1 := by
        rw [← amin x, ← amin y, he]
      have hg : x.1 = y.1 := by
        apply Subtype.ext
        rw [← (fs x).2.1, ← (fs y).2.1, he, ha]
      rcases x with ⟨g, a, v, r⟩
      rcases y with ⟨g', a', v', r'⟩
      change g = g' at hg
      change a = a' at ha
      cases hg; cases ha
      congr 1
      apply congrArg (Sigma.mk a)
      apply Prod.ext
      · apply Subtype.ext; apply Subtype.ext
        apply Prod.ext
        · apply Equiv.ext; intro i; apply Fin.ext
          change (v.val.val.1 i).val = (v'.val.val.1 i).val
          have hx := ((fs ⟨g, a, v, r⟩).2.2.1 i).1
          have hy := ((fs ⟨g, a, v', r'⟩).2.2.1 i).1
          rw [he] at hx
          exact Nat.add_left_cancel (hx.symm.trans hy)
        · apply Subtype.ext; funext i
          exact (((fs ⟨g, a, v, r⟩).2.2.1 i).2).symm.trans
            ((congrArg (fun w : C => w.val.val.2.val (lp a i)) he).trans
              ((fs ⟨g, a, v', r'⟩).2.2.1 i).2)
      · apply Subtype.ext; apply Subtype.ext
        apply Prod.ext
        · apply Equiv.ext; intro i; apply Fin.ext
          change (r.val.val.1 i).val = (r'.val.val.1 i).val
          have hx := ((fs ⟨g, a, v, r⟩).2.2.2 i).1
          have hy := ((fs ⟨g, a, v', r'⟩).2.2.2 i).1
          rw [he] at hx
          exact Nat.add_right_cancel (hx.symm.trans hy)
        · apply Subtype.ext; funext i
          exact (((fs ⟨g, a, v, r⟩).2.2.2 i).2).symm.trans
            ((congrArg (fun w : C => w.val.val.2.val (rp' a i)) he).trans
              ((fs ⟨g, a, v', r'⟩).2.2.2 i).2)
    have fj : Function.Surjective f := by
      intro w
      let a : Fin (k + 1) := w.val.val.1.symm 0
      let c := k - a.val
      let w' := resize (sizeEq a).symm w
      let z : Fin (a.val + (c + 1)) := Fin.natAdd a.val 0
      have ez : Fin.cast (sizeEq a) z = a := Fin.ext (by simp [z])
      have wp (i : Fin (a.val + (c + 1))) :
          (w'.val.val.1 i).val = (w.val.val.1 (Fin.cast (sizeEq a) i)).val := by
        have hp := rp (sizeEq a).symm w (Fin.cast (sizeEq a) i)
        exact hp
      have wg (i : Fin (a.val + (c + 1))) :
          w'.val.val.2.val i = w.val.val.2.val (Fin.cast (sizeEq a) i) := by
        have hp := rg (sizeEq a).symm w (Fin.cast (sizeEq a) i)
        exact hp
      have hz : w'.val.val.1 z = 0 := by
        apply Fin.ext; rw [wp, ez]; exact congrArg Fin.val (w.val.val.1.apply_symm_apply 0)
      obtain ⟨⟨v, r⟩, ⟨he, hv, hr⟩, _⟩ :=
        minimum_factorization w'.val.val.1 hz w'.val.property.1
      let g := w'.val.val.2.val z
      have gb : l ≤ g.val ∧ g.val ≤ h := w'.property z
      let lam : Fin a.val → Fin (m + 1) := fun i => w'.val.val.2.val (i.castAdd (c + 1))
      let ρ : Fin c → Fin (m + 1) := fun i => w'.val.val.2.val (Fin.natAdd a.val i.succ)
      have vl (i : Fin a.val) :
          (w'.val.val.1 (i.castAdd (c + 1))).val = c + 1 + (v i).val := by
        rw [← he]
        simp [c, joinUpper, blockSum, Equiv.sumComm, Nat.add_comm]
      have vr (i : Fin c) :
          (w'.val.val.1 (Fin.natAdd a.val i.succ)).val = (r i).val + 1 := by
        rw [← he]
        simp [joinUpper, blockSum, Equiv.sumComm]
      let v' : IntervalConfiguration b l g.val a.val := by
        refine ⟨⟨(v, ⟨lam, ?_⟩), hv, ?_⟩, ?_⟩
        · intro i j hij; exact w'.val.val.2.property hij
        · intro i j hij huv
          change v i < v j at huv
          apply w'.val.property.2 (i.castAdd (c + 1)) (j.castAdd (c + 1)) hij
          change (w'.val.val.1 _).val < (w'.val.val.1 _).val
          rw [vl, vl]; exact Nat.add_lt_add_left huv _
        · intro i
          exact ⟨(w'.property _).1, w'.val.val.2.property (show i.castAdd (c + 1) ≤ z by
            change i.val ≤ a.val + 0; omega)⟩
      let r' : IntervalConfiguration b g.val (min h (dead b g.val - 1)) c := by
        refine ⟨⟨(r, ⟨ρ, ?_⟩), hr, ?_⟩, ?_⟩
        · intro i j hij; apply w'.val.val.2.property; simpa using hij
        · intro i j hij huv
          change r i < r j at huv
          apply w'.val.property.2 (Fin.natAdd a.val i.succ) (Fin.natAdd a.val j.succ)
            (by simpa using hij)
          change (w'.val.val.1 _).val < (w'.val.val.1 _).val
          rw [vr, vr]; exact Nat.add_lt_add_right huv _
        · intro i
          have hd := w'.val.property.2 z (Fin.natAdd a.val i.succ)
            (by simp [z]) (by rw [hz]; change 0 < (w'.val.val.1 _).val; rw [vr]; omega)
          refine ⟨w'.val.val.2.property (show z ≤ Fin.natAdd a.val i.succ by simp [z]), ?_⟩
          have hhi := (w'.property (Fin.natAdd a.val i.succ)).2
          change (ρ i).val ≤ min h (dead b g.val - 1)
          change (ρ i).val < dead b g.val at hd
          exact le_min hhi (by omega)
      let x : D := ⟨⟨g, gb⟩, a, v', r'⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      apply Prod.ext
      · apply Equiv.ext; intro i; apply Fin.ext
        obtain ⟨j, rfl⟩ := (finCongr (sizeEq a)).surjective i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · have hfx := ((fs x).2.2.1 j).1
          have hw := wp (j.castAdd (c + 1))
          rw [vl] at hw
          exact hfx.trans hw
        · refine Fin.cases ?_ (fun j => ?_) j
          · have hfx := congrArg Fin.val (fs x).1
            have hw := wp z
            rw [hz] at hw
            simpa [x, z, ez] using hfx.trans hw
          · have hfx := ((fs x).2.2.2 j).1
            have hw := wp (Fin.natAdd a.val j.succ)
            rw [vr] at hw
            exact hfx.trans hw
      · apply Subtype.ext; funext i
        obtain ⟨j, rfl⟩ := (finCongr (sizeEq a)).surjective i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j
        · exact ((fs x).2.2.1 j).2.trans (wg (j.castAdd (c + 1)))
        · refine Fin.cases ?_ (fun j => ?_) j
          · simpa [x, z, ez] using (fs x).2.1.trans (wg z)
          · exact ((fs x).2.2.2 j).2.trans (wg (Fin.natAdd a.val j.succ))
    let ed : D ≃ SplitActual b l h k := Equiv.sigmaCongrRight (fun g =>
      Equiv.sigmaCongrRight (fun a => Equiv.prodCongr (ea l g.val.val a.val).symm
        (ea g.val.val (min h (dead b g.val.val - 1)) (k - a.val)).symm))
    let e := (ea l h (k + 1)).trans ((Equiv.ofBijective f ⟨fi, fj⟩).symm.trans ed)
    refine ⟨⟨e⟩, ?_⟩
    change Nat.card (IntervalActual b l h (k + 1)) = _
    rw [Nat.card_congr e]
    unfold SplitActual
    simp only [Nat.card_sigma, Nat.card_prod, intervalCount]
  · intro k
    unfold intervalCount count
    exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun w : Actual b k => by
      intro i
      exact ⟨Nat.zero_le _, Nat.le_of_lt_succ (gap (extractShuffle w.val) i).isLt⟩))

end

end D5.S1.Words.Patterns.A398542MinimumRecurrence
