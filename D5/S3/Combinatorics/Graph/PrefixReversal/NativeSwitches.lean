/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeSwitches
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native T and E switching words close with exact simple prefix traces. -/
import D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open Equiv

/-- The first half of the actual alternating T word, as a literal list. -/
def tHalfWord (m : ℕ) : List (Configuration m) :=
  [a m, c m] ++ (List.replicate (m - 2) [b m, c m]).flatten

private theorem bc_pow_val {m : ℕ} (hm : 2 ≤ m) (k : ℕ) (i : Fin (m + 1)) :
    (((b m * c m) ^ k) i).val =
      if i.val < m then (i.val + k) % m else i.val := by
  have hmpos : 0 < m := by omega
  induction k with
  | zero =>
    simp only [pow_zero, Equiv.Perm.one_apply, Nat.add_zero]
    by_cases hi : i.val < m
    · simp only [if_pos hi, Nat.mod_eq_of_lt hi]
    · simp only [if_neg hi]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, bc_apply hm]
    by_cases hi : i.val < m
    · have hv : (((b m * c m) ^ k) i).val = (i.val + k) % m := by
        simpa only [if_pos hi] using ih
      simp only [hv, Nat.mod_lt _ hmpos, dite_true, Fin.val_mk, if_pos hi]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rfl
    · have hv : (((b m * c m) ^ k) i).val = i.val := by
        simpa only [if_neg hi] using ih
      simp only [hv, hi, dite_false, if_false]

private theorem tHalfWord_product (m : ℕ) :
    (tHalfWord m).prod = a m * c m * (b m * c m) ^ (m - 2) := by
  simp [tHalfWord, List.prod_flatten, List.prod_replicate, mul_assoc]

/-- The halfword exchanges only the first and last positions, for every size.
This endpoint identity is computed on the actual native position permutations. -/
theorem native_t_halfword_swap {m : ℕ} (hm : 3 ≤ m) :
    (tHalfWord m).prod = Equiv.swap (0 : Fin (m + 1)) (Fin.last m) := by
  rw [tHalfWord_product]
  apply Equiv.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    apply Fin.ext
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, a_apply]
    simp only [Fin.val_rev, c_apply, bc_pow_val (by omega : 2 ≤ m), Fin.val_zero]
    simp [show 0 < m by omega, Nat.mod_eq_of_lt (show m - 2 < m by omega),
      show m - 2 < m - 1 by omega]
  · by_cases hil : i = Fin.last m
    · subst i
      apply Fin.ext
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, a_apply]
      simp [c_apply, bc_pow_val (by omega : 2 ≤ m), Fin.val_last,
        show ¬ m < m - 1 by omega]
    · have hi : i.val < m := by
        have hilv : i.val ≠ m := fun h => hil (Fin.ext h)
        omega
      have hi0v : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      apply Fin.ext
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, a_apply]
      simp only [Fin.val_rev, c_apply, bc_pow_val (by omega : 2 ≤ m), if_pos hi]
      rw [Equiv.swap_apply_of_ne_of_ne hi0 hil]
      by_cases hi1 : i.val = 1
      · simp [hi1, show 1 + (m - 2) = m - 1 by omega,
          Nat.mod_eq_of_lt (show m - 1 < m by omega)]
        omega
      · have htwo : 2 ≤ i.val := by omega
        have hmod : (i.val + (m - 2)) % m = i.val - 2 := by
          have he : i.val + (m - 2) = (i.val - 2) + m := by omega
          rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - 2 < m)]
        rw [hmod, if_pos (by omega : i.val - 2 < m - 1)]
        omega


/-- The entire native alternating T word. -/
def tWord (m : ℕ) : List (Configuration m) := tHalfWord m ++ tHalfWord m

/-- A complete supplier E uses every prefix-rotation gap once. -/
def eWord (m : ℕ) : List (Configuration m) :=
  (List.replicate m [b m, c m]).flatten

/-- The interior paired ports of either T half, in their literal order. -/
def tBlock (m : ℕ) : List (Configuration m) :=
  (List.ofFn (fun j : Fin (m - 2) =>
    [a m * c m * (b m * c m) ^ j.val,
      a m * c m * (b m * c m) ^ j.val * b m])).flatten

private theorem word_foldl {m : ℕ} (z : Configuration m)
    (l : List (Configuration m)) : l.foldl (· * ·) z = z * l.prod := by
  induction l generalizing z with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc]

private theorem pair_trace {m : ℕ} (z : Configuration m) (k : ℕ) :
    List.scanl (· * ·) z (List.replicate k [b m, c m]).flatten =
      (List.ofFn (fun j : Fin k =>
        [z * (b m * c m) ^ j.val, z * (b m * c m) ^ j.val * b m])).flatten ++
      [z * (b m * c m) ^ k] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.scanl_append, word_foldl, ih]
    rw [List.ofFn_succ_last, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    simp [List.prod_flatten, List.prod_replicate, pow_succ, mul_assoc,
      List.append_assoc]

private theorem scanl_left_mul {m : ℕ} (z w : Configuration m)
    (l : List (Configuration m)) :
    List.scanl (· * ·) (z * w) l =
      (List.scanl (· * ·) w l).map (z * ·) := by
  induction l generalizing w with
  | nil => simp
  | cons x xs ih => simp [mul_assoc, ih]

private theorem half_trace {m : ℕ} (hm : 3 ≤ m) :
    List.scanl (· * ·) (1 : Configuration m) (tHalfWord m) =
      [1, a m] ++ tBlock m ++
      [Equiv.swap (0 : Fin (m + 1)) (Fin.last m)] := by
  simp only [tHalfWord, List.cons_append, List.nil_append, List.scanl_cons,
    one_mul]
  rw [pair_trace]
  have he := native_t_halfword_swap hm
  rw [tHalfWord_product] at he
  simpa only [tBlock, he, List.cons_append, List.nil_append] using
    congrArg (fun l : List (Configuration m) => (1 : Configuration m) :: a m :: l)
      (rfl :
        (List.ofFn (fun j : Fin (m - 2) =>
          [a m * c m * (b m * c m) ^ j.val,
            a m * c m * (b m * c m) ^ j.val * b m])).flatten ++
          [a m * c m * (b m * c m) ^ (m - 2)] = _)

private theorem bc_order {m : ℕ} (hm : 3 ≤ m) : (b m * c m) ^ m = 1 := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [bc_pow_val (by omega : 2 ≤ m)]
  by_cases hi : i.val < m
  · simp [hi, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · simp [hi]

private theorem final_reflected_port {m : ℕ} (hm : 3 ≤ m) :
    a m * c m * (b m * c m) ^ (m - 1) * b m = a m := by
  have he : (b m * c m) ^ (m - 1) * (b m * c m) = 1 := by
    rw [← pow_succ, show m - 1 + 1 = m by omega, bc_order hm]
  have hc : (b m * c m) ^ (m - 1) * b m = c m := by
    have hh := congrArg (· * c m) he
    simpa only [mul_assoc, c_sq, mul_one, one_mul] using hh
  rw [mul_assoc, hc, mul_assoc, c_sq, mul_one]

private theorem prefix_port_injective {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    Function.Injective (fun p : Fin m × Bool =>
      z * (b m * c m) ^ p.1.val * (if p.2 then b m else 1)) := by
  intro p q he
  let index (r : Fin m × Bool) : Fin m × Fin (m + 1) × Bool :=
    (r.1, if r.2 then -1 else 0, r.2)
  have hcoord (r : Fin m × Bool) :
      coordinate z (index r) =
        z * (b m * c m) ^ r.1.val * (if r.2 then b m else 1) := by
    rcases r with ⟨i, s⟩
    cases s <;> simp [coordinate, index, gapAnchor, cycle_zero, b_eq_cycle_a,
      mul_assoc]
  have hsub : coordinateEquiv hm z (index p) = coordinateEquiv hm z (index q) := by
    apply Subtype.ext
    change coordinate z (index p) = coordinate z (index q)
    rw [hcoord, hcoord]
    exact he
  have hi := (coordinateEquiv hm z).injective hsub
  apply Prod.ext
  · exact congrArg (fun x : Fin m × Fin (m + 1) × Bool => x.1) hi
  · exact congrArg (fun x : Fin m × Fin (m + 1) × Bool => x.2.2) hi

private def lowerIndices {m : ℕ} (hm : 3 ≤ m) : List (Fin m × Bool) :=
  [(⟨m - 2, by omega⟩, false), (⟨m - 1, by omega⟩, true)] ++
    (List.ofFn (fun j : Fin (m - 2) =>
      [(⟨j.val, by omega⟩, false), (⟨j.val, by omega⟩, true)])).flatten

private theorem lowerIndices_nodup {m : ℕ} (hm : 3 ≤ m) :
    (lowerIndices hm).Nodup := by
  let pairs := List.ofFn (fun j : Fin (m - 2) =>
    [((⟨j.val, by omega⟩ : Fin m), false), ((⟨j.val, by omega⟩ : Fin m), true)])
  have hbody : pairs.flatten.Nodup := by
    apply List.nodup_flatten.mpr
    constructor
    · intro l hl
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
      simp
    · apply List.pairwise_ofFn.mpr
      intro i j hij
      rw [List.disjoint_left]
      intro x hx hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      all_goals
        have he := congrArg (fun p : Fin m × Bool => p.1.val) (hx.symm.trans hy)
        simp only at he
        omega
  change ([((⟨m - 2, by omega⟩ : Fin m), false),
    ((⟨m - 1, by omega⟩ : Fin m), true)] ++
    pairs.flatten).Nodup
  apply List.Nodup.append
  · simp
  · exact hbody
  · rw [List.disjoint_left]
    intro x hx hy
    obtain ⟨l, hl, hxl⟩ := List.mem_flatten.mp hy
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hxl
    rcases hx with hx | hx <;> rcases hxl with hy | hy
    all_goals
      have he := congrArg (fun p : Fin m × Bool => p.1.val) (hx.symm.trans hy)
      simp only at he
      have hj := j.isLt
      omega

private theorem lower_trace_nodup {m : ℕ} (hm : 3 ≤ m) :
    ([Equiv.swap (0 : Fin (m + 1)) (Fin.last m), a m] ++ tBlock m).Nodup := by
  have hd := (lowerIndices_nodup hm).map
    (prefix_port_injective hm (a m * c m))
  have he := native_t_halfword_swap hm
  rw [tHalfWord_product] at he
  simpa [lowerIndices, tBlock, List.map_flatten, he, Function.comp_def,
    final_reflected_port hm] using hd

private theorem full_trace {m : ℕ} (hm : 3 ≤ m) :
    List.scanl (· * ·) (1 : Configuration m) (tWord m) =
      [1, a m] ++ tBlock m ++
      [Equiv.swap (0 : Fin (m + 1)) (Fin.last m),
        Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * a m] ++
      (tBlock m).map (Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * ·) ++ [1] := by
  rw [tWord, List.scanl_append, word_foldl, one_mul, native_t_halfword_swap hm]
  have hl := scanl_left_mul
    (Equiv.swap (0 : Fin (m + 1)) (Fin.last m)) 1 (tHalfWord m)
  simp only [mul_one] at hl
  rw [hl, half_trace hm]
  simp [List.append_assoc]

private theorem lower_last {m : ℕ} (hm : 3 ≤ m) (v : Configuration m)
    (hv : v ∈ [Equiv.swap (0 : Fin (m + 1)) (Fin.last m), a m] ++ tBlock m) :
    v (Fin.last m) = 0 := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (rfl | rfl) | hv
  · simp
  · simp [a_apply]
  · obtain ⟨l, hl, hvl⟩ := List.mem_flatten.mp hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
    have hp : ((b m * c m) ^ j.val) (Fin.last m) = Fin.last m := by
      apply Fin.ext
      simp [bc_pow_val (by omega : 2 ≤ m)]
    have hc : c m (Fin.last m) = Fin.last m := by
      apply Fin.ext
      simp [c_apply]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvl
    rcases hvl with rfl | rfl
    · simp [Equiv.Perm.mul_apply, hp, hc, a_apply]
    · simp [Equiv.Perm.mul_apply, b_last, hp, hc, a_apply]

/-- The literal T word returns to the starting configuration, and every vertex
before that return is different. This proves the native simple polygon for all
sizes, rather than assuming the cut-port pairing. -/
theorem native_t_simple_trace {m : ℕ} (hm : 3 ≤ m) :
    (tWord m).prod = 1 ∧
      (List.scanl (· * ·) (1 : Configuration m) (tWord m)).dropLast.Nodup := by
  constructor
  · simp [tWord, native_t_halfword_swap hm]
  · let τ : Configuration m := Equiv.swap 0 (Fin.last m)
    let lower := [τ, a m] ++ tBlock m
    have hlow : lower.Nodup := lower_trace_nodup hm
    have hupp : (lower.map (τ * ·)).Nodup :=
      hlow.map (fun x y h => mul_left_cancel h)
    have hd : List.Disjoint lower (lower.map (τ * ·)) := by
      rw [List.disjoint_left]
      intro x hx hy
      obtain ⟨y, hyLower, rfl⟩ := List.mem_map.mp hy
      have hxl := lower_last hm (τ * y) hx
      have hyl := lower_last hm y hyLower
      have hzero : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_zero, Fin.val_last] at hv
        omega
      simp only [Equiv.Perm.mul_apply, hyl, τ, Equiv.swap_apply_left] at hxl
      exact hzero hxl.symm
    have hn := hlow.append hupp hd
    have he : lower ++ lower.map (τ * ·) =
        τ :: (a m :: tBlock m) ++ (1 : Configuration m) ::
          (τ * a m :: (tBlock m).map (τ * ·)) := by
      simp [lower, τ]
    rw [he] at hn
    have hp : List.Perm
        ((1 : Configuration m) :: (a m :: tBlock m) ++
          τ :: (τ * a m :: (tBlock m).map (τ * ·)))
        (τ :: (a m :: tBlock m) ++ (1 : Configuration m) ::
          (τ * a m :: (tBlock m).map (τ * ·))) := List.cons_append_cons_perm
    rw [full_trace hm]
    rw [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
    simpa only [τ, List.append_assoc, List.cons_append,
      List.nil_append] using hp.nodup_iff.mpr hn

/-- The complete E supplier is an actual closed simple alternating polygon at
every native starting tuple. It contains all prefix-rotation ports, in order. -/
theorem native_e_simple_trace {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    (eWord m).prod = 1 ∧
      List.scanl (· * ·) z (eWord m) =
        (List.ofFn (fun j : Fin m =>
          [z * (b m * c m) ^ j.val, z * (b m * c m) ^ j.val * b m])).flatten ++ [z] ∧
      (List.scanl (· * ·) z (eWord m)).dropLast.Nodup := by
  have ht : List.scanl (· * ·) z (eWord m) =
      (List.ofFn (fun j : Fin m =>
        [z * (b m * c m) ^ j.val, z * (b m * c m) ^ j.val * b m])).flatten ++ [z] := by
    simpa only [eWord, bc_order hm, mul_one] using pair_trace z m
  refine ⟨?_, ht, ?_⟩
  · simp [eWord, List.prod_flatten, List.prod_replicate, bc_order hm]
  · rw [ht, List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
    let pairs := List.ofFn (fun j : Fin m => [(j, false), (j, true)])
    have hindices : pairs.flatten.Nodup := by
      apply List.nodup_flatten.mpr
      constructor
      · intro l hl
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
        simp
      · apply List.pairwise_ofFn.mpr
        intro i j hij
        rw [List.disjoint_left]
        intro x hx hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        all_goals
          have he := congrArg (fun p : Fin m × Bool => p.1.val) (hx.symm.trans hy)
          simp only at he
          have hij' : i.val < j.val := hij
          omega
    have hd := hindices.map (prefix_port_injective hm z)
    simpa [pairs, List.map_flatten, Function.comp_def] using hd

#print axioms native_t_halfword_swap
#print axioms native_t_simple_trace
#print axioms native_e_simple_trace

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
