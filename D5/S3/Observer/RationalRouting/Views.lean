/- GID: D5/S3/Observer/RationalRouting/Views
   generality: I
   mirror-B: D5/B/S3/Observer/RationalRouting/Views
   mirror-E: none(waiver:finite-exact-view-encodings)
   anchors: []
   utility: none
   digest: Subtractive decoding retains the original rational, chronology, named path and indexed memory. -/

import D5.S3.Observer.RationalRouting.Source

/-! Finite actual-image encodings of the original rooted rational history. -/

set_option autoImplicit false

namespace D5.S3.Observer.RationalRouting

abbrev PositivePair := ℕ × ℕ

def pairStep (b : Bool) (p : PositivePair) : PositivePair :=
  if b then (p.1+p.2,p.2) else (p.1,p.1+p.2)

def encode (w : List Bool) : PositivePair := w.foldl (fun p b => pairStep b p) (1,1)

def ratio (p : PositivePair) : ℚ := (p.1 : ℚ)/p.2

/-- The last inverse label is appended, so the result is chronological. -/
def decodePair (p q : ℕ) : List Bool :=
  if p = 0 ∨ q = 0 then []
  else if p = q then []
  else if p < q then decodePair p (q-p) ++ [false]
  else decodePair (p-q) q ++ [true]
termination_by p+q
decreasing_by all_goals omega

def originalWord (x : ℚ) : List Bool := decodePair x.num.natAbs x.den

structure NamedEdge where
  fromIndex : ℕ
  toIndex : ℕ
  letter : Bool
  fromPair : PositivePair
  toPair : PositivePair
  deriving DecidableEq

structure NamedPath where
  root : ℕ × PositivePair
  tip : ℕ × PositivePair
  edges : List NamedEdge
  deriving DecidableEq

def path (w : List Bool) : NamedPath where
  root := (0,(1,1))
  tip := (w.length,encode w)
  edges := w.zipIdx.map (fun bk => ⟨bk.2,bk.2+1,bk.1,
    encode (w.take bk.2),encode (w.take (bk.2+1))⟩)

/-- Indices and every prefix pair, including root and final row, are retained. -/
def memory (w : List Bool) : List (ℕ × PositivePair) :=
  (List.range (w.length+1)).map (fun k => (k,encode (w.take k)))

inductive View | B | T | S | M | full

def ViewOutput : View → Type
  | .B => ℚ
  | .T => List Bool
  | .S => NamedPath
  | .M => List (ℕ × PositivePair)
  | .full => ℚ × List Bool × NamedPath × List (ℕ × PositivePair)

def originalView : (V : View) → ℚ → ViewOutput V
  | .B, x => x
  | .T, x => originalWord x
  | .S, x => path (originalWord x)
  | .M, x => memory (originalWord x)
  | .full, x => (x,originalWord x,path (originalWord x),memory (originalWord x))

def recoverView : (V : View) → ViewOutput V → ℚ
  | .B, x => x
  | .T, w => ratio (encode w)
  | .S, p => ratio (encode (p.edges.map NamedEdge.letter))
  | .M, m => ratio ((m.getLast?).getD (0,(1,1))).2
  | .full, x => x.1

private theorem encode_append (w : List Bool) (b : Bool) :
    encode (w++[b]) = pairStep b (encode w) := by
  simp [encode,List.foldl_append]

private theorem encode_good (w : List Bool) :
    0 < (encode w).1 ∧ 0 < (encode w).2 ∧ (encode w).1.Coprime (encode w).2 := by
  induction w using List.reverseRecOn with
  | nil => norm_num [encode]
  | append_singleton w b ih =>
    rw [encode_append]
    cases b <;> simp only [pairStep, Bool.false_eq_true, ↓reduceIte]
    · exact ⟨ih.1,by omega,Nat.coprime_self_add_right.mpr ih.2.2⟩
    · exact ⟨by omega,ih.2.1,Nat.coprime_add_self_left.mpr ih.2.2⟩

private theorem encode_decode (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : p.Coprime q) : encode (decodePair p q) = (p,q) := by
  induction hsum : p+q using Nat.strong_induction_on generalizing p q with
  | h n ih =>
    rw [decodePair,if_neg (by omega)]
    by_cases heq : p = q
    · subst q
      have hp1 : p = 1 := by simpa [Nat.Coprime] using hc
      subst p
      simp [encode]
    · rw [if_neg heq]
      by_cases hlt : p < q
      · rw [if_pos hlt,encode_append]
        have hsub : p.Coprime (q-p) := (Nat.coprime_sub_self_right hlt.le).mpr hc
        rw [ih (p+(q-p)) (by omega) p (q-p) hp (by omega) hsub rfl]
        simp only [pairStep, Bool.false_eq_true, ↓reduceIte]
        congr 1 <;> omega
      · rw [if_neg hlt,encode_append]
        have hsub : (p-q).Coprime q := (Nat.coprime_sub_self_left (by omega)).mpr hc
        rw [ih ((p-q)+q) (by omega) (p-q) q (by omega) hq hsub rfl]
        simp only [pairStep, ↓reduceIte]
        congr 1 <;> omega

private theorem decode_encode (w : List Bool) :
    decodePair (encode w).1 (encode w).2 = w := by
  induction w using List.reverseRecOn with
  | nil => simp [encode,decodePair]
  | append_singleton w b ih =>
    obtain ⟨hp,hq,hc⟩ := encode_good w
    rw [encode_append]
    cases b <;> simp only [pairStep, Bool.false_eq_true, ↓reduceIte]
    · rw [decodePair,if_neg (by omega),if_neg (by omega),if_pos (by omega)]
      simpa using congrArg (fun u => u++[false]) ih
    · rw [decodePair,if_neg (by omega),if_neg (by omega),if_neg (by omega)]
      simpa using congrArg (fun u => u++[true]) ih

private theorem original_pair (x : ℚ) (hx : 0 < x) :
    encode (originalWord x) = (x.num.natAbs,x.den) := by
  apply encode_decode
  · have h := Rat.num_pos.mpr hx
    exact Int.natAbs_pos.mpr (ne_of_gt h)
  · exact x.den_pos
  · exact x.reduced

private theorem rational_reconstruction (x : ℚ) (hx : 0 < x) :
    ratio (encode (originalWord x)) = x := by
  rw [original_pair x hx]
  have habs : (x.num.natAbs : ℚ) = (x.num : ℚ) := by
    have hn := Rat.num_pos.mpr hx
    have hh : (x.num.natAbs : ℤ) = x.num := by
      rw [Int.natCast_natAbs,abs_of_nonneg hn.le]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hh
  simpa [ratio,habs] using Rat.num_div_den x

private theorem path_letters (w : List Bool) : (path w).edges.map NamedEdge.letter = w := by
  simp [path,List.map_map,Function.comp_def,List.zipIdx_map_fst]

private theorem memory_final (w : List Bool) :
    (memory w).getLast? = some (w.length,encode w) := by
  simp [memory,List.range_succ,List.map_append]

private theorem pair_ratio_step (b : Bool) (p : PositivePair)
    (hp : 0 < p.1) (hq : 0 < p.2) :
    ratio (pairStep b p) = step b (ratio p) := by
  have hq' : (p.2 : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  cases b <;> dsimp [ratio,pairStep,step]
  · push_cast
    field_simp
    <;> ring
  · push_cast
    field_simp [hq']
    <;> ring

private theorem ratio_fold (w : List Bool) (p : PositivePair)
    (hp : 0 < p.1) (hq : 0 < p.2) :
    ratio (w.foldl (fun p b => pairStep b p) p) = attain w (ratio p) := by
  induction w generalizing p with
  | nil => rfl
  | cons b w ih =>
    simp only [List.foldl_cons,attain]
    have hgood : 0 < (pairStep b p).1 ∧ 0 < (pairStep b p).2 := by
      cases b <;> simp only [pairStep,Bool.false_eq_true,↓reduceIte] <;>
        constructor <;> omega
    rw [ih _ hgood.1 hgood.2,pair_ratio_step b p hp hq]

private theorem word_rational_roundtrip (w : List Bool) :
    originalWord (ratio (encode w)) = w := by
  obtain ⟨hp,hq,hc⟩ := encode_good w
  let p := (encode w).1
  let q := (encode w).2
  have hc' : (p : ℤ).natAbs.Coprime (q : ℤ).natAbs := by simpa using hc
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hnum : ((p : ℚ)/q).num = (p : ℤ) := by
    simpa only [Int.cast_natCast] using
      (Rat.num_div_eq_of_coprime (a := (p : ℤ)) (b := (q : ℤ)) hq' hc')
  have hden : ((p : ℚ)/q).den = q := by
    have hh : ((((p : ℚ)/q).den : ℕ) : ℤ) = (q : ℤ) := by
      simpa only [Int.cast_natCast] using
        (Rat.den_div_eq_of_coprime (a := (p : ℤ)) (b := (q : ℤ)) hq' hc')
    exact_mod_cast hh
  dsimp [originalWord,ratio]
  rw [hnum,hden,Int.natAbs_natCast]
  exact decode_encode w

/-- Exact decoders on all positive rational actual images, with the literal
chronological word, rooted named-edge path and all indexed prefix pairs.
The pair decoder and encoder are mutual inverses on their declared domains. -/
theorem original_views_reconstruct :
    (∀ (p q : ℕ), 0 < p → 0 < q → p.Coprime q → encode (decodePair p q) = (p,q)) ∧
    (∀ w : List Bool, decodePair (encode w).1 (encode w).2 = w) ∧
    (∀ (V : View) (x : ℚ), 0 < x → recoverView V (originalView V x) = x) ∧
    (∀ w : List Bool, ratio (encode w) = attain w 1) ∧
    (∀ w : List Bool, originalWord (ratio (encode w)) = w) := by
  refine ⟨encode_decode,decode_encode,?_,?_,word_rational_roundtrip⟩
  · intro V x hx
    cases V
    · rfl
    · exact rational_reconstruction x hx
    · simp only [originalView,recoverView,path_letters]
      exact rational_reconstruction x hx
    · simp only [originalView,recoverView,memory_final,Option.getD_some]
      exact rational_reconstruction x hx
    · rfl
  · intro w
    simpa [encode,ratio] using ratio_fold w (1,1) (by norm_num) (by norm_num)

#print axioms original_views_reconstruct

end D5.S3.Observer.RationalRouting
