/- GID: D5/S3/Combinatorics/Graph/SeymourSharpness/Family
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SeymourSharpness/Family
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The all-parameter decreasing-block family of oriented graphs. -/

module

public import D5.S3.Combinatorics.Graph.SeymourSharpness.Circulant

/-! A cycle of independent and short-arc circulant blocks. -/

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.SeymourSharpness

abbrev Block (r : ℕ) := ZMod (r + 3)

def cycle (r : ℕ) (i j : Block r) : Prop := j = i + 1

def blockSize (q r : ℕ) (i : Block r) : ℕ :=
  if i.val = 0 then q else if i.val ≤ r + 1 then 3 * r + 3 - i.val else 6 * r + 5

private lemma block_pos (q r : ℕ) [NeZero q] (i : Block r) : 0 < blockSize q r i := by
  have hq := NeZero.pos q
  unfold blockSize
  split_ifs <;> omega

instance blockNeZero (q r : ℕ) [NeZero q] (i : Block r) : NeZero (blockSize q r i) :=
  ⟨Nat.ne_of_gt (block_pos q r i)⟩

abbrev Vertex (q r : ℕ) := (i : Block r) × ZMod (blockSize q r i)

def internal (q r : ℕ) (i : Block r) (a b : ZMod (blockSize q r i)) : Prop :=
  i ≠ 0 ∧ circulant (blockSize q r i) a b

def family (q r : ℕ) : Vertex q r → Vertex q r → Prop :=
  composition (cycle r) (internal q r)

def internalDegree (q r : ℕ) (i : Block r) : ℕ :=
  if i = 0 then 0 else half (blockSize q r i)

private lemma shift_ne (r k : ℕ) (i : Block r) (hk : 0 < k) (hkr : k < r + 3) :
    i + (k : Block r) ≠ i := by
  intro h
  have he : (k : Block r) = 0 := add_left_cancel (h.trans (add_zero i).symm)
  have hv := congrArg ZMod.val he
  rw [ZMod.val_natCast_of_lt hkr,ZMod.val_zero] at hv
  omega

private lemma cycle_asymm (r : ℕ) : ∀ ⦃i j⦄, cycle r i j → ¬ cycle r j i := by
  intro i j hij hji
  change j = i + 1 at hij
  change i = j + 1 at hji
  apply shift_ne r 2 i (by omega) (by omega)
  calc i + 2 = (i + 1) + 1 := by abel
       _ = j + 1 := by rw [hij]
       _ = i := hji.symm

private lemma cycle_second (r : ℕ) (i j : Block r) :
    ExactSecond (cycle r) i j ↔ j = i + 2 := by
  constructor
  · rintro ⟨_,_,⟨k,hik,hkj⟩⟩
    change k = i + 1 at hik
    change j = k + 1 at hkj
    rw [hkj,hik]
    abel
  · intro h
    subst j
    refine ⟨shift_ne r 2 i (by omega) (by omega),?_,⟨i + 1,rfl,?_⟩⟩
    · intro he
      change i + 2 = i + 1 at he
      have h21 : (2 : Block r) = 1 := add_left_cancel he
      have hv := congrArg ZMod.val h21
      have h2 : (2 : Block r).val = 2 :=
        ZMod.val_natCast_of_lt (n := r + 3) (a := 2) (by omega)
      have h1 : (1 : Block r).val = 1 :=
        ZMod.val_natCast_of_lt (n := r + 3) (a := 1) (by omega)
      omega
    · change i + 2 = (i + 1) + 1
      abel

private lemma internal_degrees (q r : ℕ) [NeZero q] (i : Block r)
    (a : ZMod (blockSize q r i)) :
    outDegree (internal q r i) a = internalDegree q r i ∧
    secondDegree (internal q r i) a = internalDegree q r i := by
  classical
  by_cases hi : i = 0
  · simp [internal,hi,internalDegree,outDegree,secondDegree,ExactSecond]
  · have he : internal q r i = circulant (blockSize q r i) := by
      funext a b
      simp [internal,hi]
    rw [he]
    simpa [internalDegree,hi] using circulant_degrees (blockSize q r i) a

theorem family_asymm (q r : ℕ) :
    ∀ ⦃x y⦄, family q r x y → ¬ family q r y x := by
  apply composition_asymm _ _ (cycle_asymm r)
  intro i a b hab hba
  have hpos : 0 < blockSize q r i := by
    have hi : i.val ≠ 0 := fun h => hab.1 ((ZMod.val_eq_zero i).mp h)
    unfold blockSize
    rw [ite_eq_right hi]
    split_ifs <;> omega
  letI : NeZero (blockSize q r i) := ⟨Nat.ne_of_gt hpos⟩
  exact circulant_asymm (blockSize q r i) hab.2 hba.2

/-- These are cardinalities of the graph's literal neighborhoods. -/
theorem family_degrees (q r : ℕ) [NeZero q] (x : Vertex q r) :
    outDegree (family q r) x = internalDegree q r x.1 + blockSize q r (x.1 + 1) ∧
    secondDegree (family q r) x = internalDegree q r x.1 + blockSize q r (x.1 + 2) := by
  rcases x with ⟨i,a⟩
  have h := composition_degrees (cycle r) (internal q r) (cycle_asymm r)
    (fun _ => inferInstance) i (i + 1) (i + 2) a (fun _ => Iff.rfl) (cycle_second r i)
  simpa only [family,(internal_degrees q r i a).1,(internal_degrees q r i a).2,
    Nat.card_zmod] using h

private lemma val_shift (r k : ℕ) (i : Block r) (h : i.val + k < r + 3) :
    (i + (k : Block r)).val = i.val + k := by
  have hk : ((k : ℕ) : Block r).val = k :=
    ZMod.val_natCast_of_lt (n := r + 3) (by omega)
  rw [ZMod.val_add, hk, Nat.mod_eq_of_lt h]

private lemma walk_block_le (q r : ℕ) {k : ℕ} {x y : Vertex q r}
    (h : Walk (family q r) k x y) (hsmall : x.1.val + k < r + 3) :
    y.1.val ≤ x.1.val + k := by
  induction h with
  | nil x => omega
  | @cons k x y z hxy hyz ih =>
    have hstep : y.1.val ≤ x.1.val + 1 := by
      rcases x with ⟨i,a⟩
      rcases y with ⟨j,b⟩
      change j.val ≤ i.val + 1
      change i.val + (k + 1) < r + 3 at hsmall
      rcases hxy with hcross | ⟨h,hinternal⟩
      · change j = i + 1 at hcross
        rw [hcross]
        have hv := val_shift r 1 i (by simpa using (show i.val + 1 < r + 3 by omega))
        simpa using hv.le
      · change j = i at h
        rw [h]
        omega
    have hsmall' : y.1.val + k < r + 3 := by omega
    have hz := ih hsmall'
    omega

private lemma walk_lift (q r k : ℕ) (x : Vertex q r) :
    ∃ y : Vertex q r, y.1 = x.1 + (k : Block r) ∧ Walk (family q r) k x y := by
  induction k generalizing x with
  | zero => exact ⟨x,by simp,Walk.nil x⟩
  | succ k ih =>
    let y : Vertex q r := ⟨x.1 + 1,0⟩
    obtain ⟨z,hz,hwalk⟩ := ih y
    have hxy : family q r x y := Or.inl rfl
    refine ⟨z,?_,Walk.cons hxy hwalk⟩
    rw [hz]
    dsimp [y]
    push_cast
    abel

private lemma size_middle (q r : ℕ) (i : Block r) (hpos : 0 < i.val)
    (hle : i.val ≤ r + 1) : blockSize q r i = 3 * r + 3 - i.val := by
  simp only [blockSize,ite_eq_right (by omega : i.val ≠ 0),ite_eq_left hle]

private lemma size_last (q r : ℕ) (i : Block r) (hval : i.val = r + 2) :
    blockSize q r i = 6 * r + 5 := by
  simp only [blockSize,hval,ite_eq_right (by omega : r + 2 ≠ 0),
    ite_eq_right (by omega : ¬ r + 2 ≤ r + 1)]

private lemma minimum_iff (q r : ℕ) [NeZero q] (x : Vertex q r) :
    3 * r + 2 ≤ outDegree (family q r) x ∧
    (outDegree (family q r) x = 3 * r + 2 ↔ x.1 = 0) := by
  have hd := (family_degrees q r x).1
  have hi := ZMod.val_lt x.1
  have hq := NeZero.pos q
  have hv1 : (1 : Block r).val = 1 :=
    ZMod.val_natCast_of_lt (n := r + 3) (a := 1) (by omega)
  by_cases hzero : x.1 = 0
  · have hsize : blockSize q r (x.1 + 1) = 3 * r + 2 := by
      simp [hzero,blockSize,hv1]
    have hdeg : outDegree (family q r) x = 3 * r + 2 := by
      simpa only [internalDegree,ite_eq_left hzero,hsize,Nat.zero_add] using hd
    exact ⟨hdeg.ge,by simp [hdeg,hzero]⟩
  · have hpos : 0 < x.1.val :=
      Nat.pos_of_ne_zero (fun h => hzero ((ZMod.val_eq_zero _).mp h))
    have hint : internalDegree q r x.1 = half (blockSize q r x.1) :=
      ite_eq_right hzero
    by_cases hlow : x.1.val ≤ r
    · have hvnext : (x.1 + 1).val = x.1.val + 1 := by
        simpa using val_shift r 1 x.1 (by omega)
      have hs := size_middle q r x.1 hpos (by omega)
      have hn := size_middle q r (x.1 + 1) (by omega) (by omega)
      rw [hvnext] at hn
      rw [hint,hs,hn] at hd
      unfold half at hd
      have hstrict : 3 * r + 2 < outDegree (family q r) x := by omega
      exact ⟨hstrict.le,by simp only [hzero,iff_false]; omega⟩
    · by_cases hend : x.1.val = r + 1
      · have hvnext : (x.1 + 1).val = x.1.val + 1 := by
          simpa using val_shift r 1 x.1 (by omega)
        have hs := size_middle q r x.1 hpos (by omega)
        have hn := size_last q r (x.1 + 1) (by omega)
        rw [hint,hs,hn] at hd
        unfold half at hd
        have hstrict : 3 * r + 2 < outDegree (family q r) x := by omega
        exact ⟨hstrict.le,by simp only [hzero,iff_false]; omega⟩
      · have hlast : x.1.val = r + 2 := by omega
        have hs := size_last q r x.1 hlast
        have hvnext : (x.1 + 1).val = 0 := by
          rw [ZMod.val_add,hlast,hv1]
          exact Nat.mod_self (r + 3)
        have hn : blockSize q r (x.1 + 1) = q := by simp [blockSize,hvnext]
        rw [hint,hs,hn] at hd
        unfold half at hd
        have hstrict : 3 * r + 2 < outDegree (family q r) x := by omega
        exact ⟨hstrict.le,by simp only [hzero,iff_false]; omega⟩

private lemma bad_before (q r : ℕ) [NeZero q] (x : Vertex q r) (hx : x.1.val < r) :
    ¬ Good (family q r) x := by
  have hv1 : (x.1 + 1).val = x.1.val + 1 := by
    simpa using val_shift r 1 x.1 (by omega)
  have hv2 : (x.1 + 2).val = x.1.val + 2 := by
    simpa using val_shift r 2 x.1 (by omega)
  have hn1 := size_middle q r (x.1 + 1) (by omega) (by omega)
  have hn2 := size_middle q r (x.1 + 2) (by omega) (by omega)
  have hdeg := family_degrees q r x
  rw [hv1] at hn1
  rw [hv2] at hn2
  unfold Good
  rw [hdeg.1,hdeg.2,hn1,hn2]
  omega

private lemma good_at (q r : ℕ) [NeZero q] (x : Vertex q r)
    (hx : x.1.val = r) : Good (family q r) x := by
  have hv1 : (x.1 + 1).val = x.1.val + 1 := by
    simpa using val_shift r 1 x.1 (by omega)
  have hv2 : (x.1 + 2).val = x.1.val + 2 := by
    simpa using val_shift r 2 x.1 (by omega)
  have hn1 := size_middle q r (x.1 + 1) (by omega) (by omega)
  have hn2 := size_last q r (x.1 + 2) (by omega)
  have hdeg := family_degrees q r x
  rw [hv1,hx] at hn1
  unfold Good
  rw [hdeg.1,hdeg.2,hn1,hn2]
  omega

/-- The dependent finite carrier realizes all clauses of the sharpness family. -/
theorem family_sharpness (q r : ℕ) [NeZero q] :
    (∀ x, 3 * r + 2 ≤ outDegree (family q r) x) ∧
    Nat.card {x : Vertex q r // outDegree (family q r) x = 3 * r + 2} = q ∧
    ∀ v : Vertex q r, outDegree (family q r) v = 3 * r + 2 →
      (∃ w, Good (family q r) w ∧ Walk (family q r) r v w) ∧
      (∀ w, Good (family q r) w → ∀ k, Walk (family q r) k v w → r ≤ k) := by
  refine ⟨fun x => (minimum_iff q r x).1,?_,?_⟩
  · rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => (minimum_iff q r x).2))]
    rw [Nat.card_congr (Equiv.sigmaSubtype (0 : Block r)),Nat.card_zmod]
    simp [blockSize]
  · intro v hv
    have hroot := (minimum_iff q r v).2.mp hv
    constructor
    · obtain ⟨w,hw,hwalk⟩ := walk_lift q r r v
      refine ⟨w,good_at q r w ?_,hwalk⟩
      rw [hw,hroot,zero_add]
      exact ZMod.val_natCast_of_lt (n := r + 3) (by omega)
    · intro w hw k hwalk
      by_contra hlt
      have hzero : v.1.val = 0 := (ZMod.val_eq_zero _).mpr hroot
      have hbound := walk_block_le q r hwalk (by omega)
      exact bad_before q r w (by omega) hw

private lemma walk_map {V W : Type*} {R : V → V → Prop} {S : W → W → Prop}
    (f : V → W) (hf : ∀ ⦃x y⦄, R x y → S (f x) (f y))
    {k : ℕ} {x y : V} (h : Walk R k x y) : Walk S k (f x) (f y) := by
  induction h with
  | nil x => exact Walk.nil (f x)
  | cons hxy hyz ih => exact Walk.cons (hf hxy) ih

/-- For every positive pair of parameters, a single finite oriented graph has
exactly the prescribed minimum roots and exact nearest - Seymour distance. -/
theorem exists_sharpness (q r : ℕ) (hq : 1 ≤ q) :
    ∃ (n : ℕ) (R : Fin n → Fin n → Prop),
      (∀ ⦃x y⦄, R x y → ¬ R y x) ∧
      (∀ x, 3 * r + 2 ≤ outDegree R x) ∧
      Nat.card {x : Fin n // outDegree R x = 3 * r + 2} = q ∧
      ∀ v : Fin n, outDegree R v = 3 * r + 2 →
        (∃ w, Good R w ∧ Walk R r v w) ∧
        (∀ w, Good R w → ∀ k, Walk R k v w → r ≤ k) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  let V := Vertex q r
  let n := Fintype.card V
  let e : V ≃ Fin n := Fintype.equivFin V
  let R : Fin n → Fin n → Prop := fun x y => family q r (e.symm x) (e.symm y)
  have hd (x : Fin n) : outDegree R x = outDegree (family q r) (e.symm x) :=
    Nat.card_congr (e.symm.subtypeEquiv (fun _ => Iff.rfl))
  have he (x z : Fin n) : ExactSecond R x z ↔
      ExactSecond (family q r) (e.symm x) (e.symm z) := by
    constructor
    · rintro ⟨hne,hnadj,⟨y,hxy,hyz⟩⟩
      exact ⟨fun h => hne (e.symm.injective h),hnadj,⟨e.symm y,hxy,hyz⟩⟩
    · rintro ⟨hne,hnadj,⟨y,hxy,hyz⟩⟩
      refine ⟨fun h => hne (congrArg e.symm h),hnadj,⟨e y,?_,?_⟩⟩
      · simpa only [R,e.symm_apply_apply] using hxy
      · simpa only [R,e.symm_apply_apply] using hyz
  have hs (x : Fin n) : secondDegree R x = secondDegree (family q r) (e.symm x) :=
    Nat.card_congr (e.symm.subtypeEquiv (he x))
  have hg (x : Fin n) : Good R x ↔ Good (family q r) (e.symm x) := by
    unfold Good
    rw [hd,hs]
  obtain ⟨hmin,hcount,hroot⟩ := family_sharpness q r
  refine ⟨n,R,?_,?_,?_,?_⟩
  · intro x y hxy hyx
    exact family_asymm q r hxy hyx
  · intro x
    rw [hd]
    exact hmin _
  · have hc : Nat.card {x : Fin n // outDegree R x = 3 * r + 2} =
        Nat.card {x : V // outDegree (family q r) x = 3 * r + 2} :=
      Nat.card_congr (e.symm.subtypeEquiv (fun x => by rw [hd]))
    exact hc.trans hcount
  · intro v hv
    obtain ⟨hupper,hlower⟩ := hroot (e.symm v) ((hd v).symm.trans hv)
    constructor
    · obtain ⟨w,hw,hwalk⟩ := hupper
      refine ⟨e w,(hg (e w)).mpr (by simpa only [e.symm_apply_apply] using hw),?_⟩
      have hm := walk_map e (S := R) (fun _ _ h => by
        simpa only [R,e.symm_apply_apply] using h) hwalk
      simpa only [e.apply_symm_apply] using hm
    · intro w hw k hwalk
      exact hlower (e.symm w) ((hg w).mp hw) k (walk_map e.symm (fun _ _ h => h) hwalk)

end D5.S3.Combinatorics.Graph.SeymourSharpness
