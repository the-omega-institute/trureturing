/- GID: D5/S3/Combinatorics/Circle/TwoNegativeJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/TwoNegativeJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange, mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Native common-cut two-negative lift for the asymmetric dyadic source. -/
import D5.S3.Combinatorics.Circle.RunFirstEarTransport
import D5.S3.Combinatorics.Circle.DyadicPrefix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.TwoNegativeJointLift
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators

private theorem positive_strip {α : Type*} {f : α → ℤ} {B h : ℤ} {l : List α}
    (hp : ∀ x ∈ l, 0 ≤ f x) (hh : 0 ≤ h) (hend : h + (l.map f).sum ≤ B) :
    InStrip f B h l := by
  apply inStrip_reflect
  apply inStrip_nonpos
  · intro x hx; have := hp x hx; omega
  · omega
  · rw [sum_neg_map]; omega

/-- Positivity controls the interiors; the two seam heights control the whole word. -/
private theorem two_blocks {α : Type*} (f : α → ℤ) (B : ℤ)
    (E F : List α) (x y : α)
    (hE : ∀ i ∈ E, 0 ≤ f i) (hF : ∀ i ∈ F, 0 ≤ f i)
    (htotal : (E.map f).sum + f x + (F.map f).sum + f y = 0)
    (hp : 0 ≤ (E.map f).sum ∧ (E.map f).sum ≤ B)
    (hx : 0 ≤ (E.map f).sum + f x)
    (hy : 0 ≤ -f y ∧ -f y ≤ B) :
    InStrip f B 0 (E ++ [x] ++ F ++ [y]) := by
  simp only [List.append_assoc, List.singleton_append, List.cons_append]
  apply inStrip_append (positive_strip hE (by omega) (by omega))
  change 0 ≤ 0 + (E.map f).sum ∧ 0 + (E.map f).sum ≤ B ∧ _
  refine ⟨by omega, by omega, ?_⟩
  apply inStrip_append (positive_strip hF (by omega) (by omega))
  change 0 ≤ 0 + (E.map f).sum + f x + (F.map f).sum ∧
    0 + (E.map f).sum + f x + (F.map f).sum ≤ B ∧ _
  simp only [InStrip]
  omega

private theorem split_perm {k : ℕ} (E : Finset (Fin k)) (x y : Fin k)
    (hxy : x ≠ y) (hx : x ∉ E) (hy : y ∉ E) :
    (E.toList ++ (Finset.univ \ (E ∪ {x,y})).toList ++ [x,y]).Perm
      (List.finRange k) := by
  classical
  let F := Finset.univ \ (E ∪ {x,y})
  have hEF : List.Disjoint E.toList F.toList := by
    apply List.disjoint_left.mpr
    intro i hi hj
    have hh := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hj)).2
    exact hh (Finset.mem_union_left _ (Finset.mem_toList.mp hi))
  have hN : (E.toList ++ F.toList ++ [x,y]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.nodup_append.mpr ⟨E.nodup_toList, F.nodup_toList,
      fun a ha b hb hab => List.disjoint_left.mp hEF ha (hab ▸ hb)⟩,
      by simp [hxy], ?_⟩
    intro i hi j hj hij
    subst j
    simp only [List.mem_append, Finset.mem_toList] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hi with hi | hi
    · rcases hj with rfl | rfl <;> contradiction
    · have hh := (Finset.mem_sdiff.mp hi).2
      exact hh (Finset.mem_union_right _ (by simpa using hj))
  apply (List.perm_ext_iff_of_nodup hN (List.nodup_finRange k)).mpr
  intro i
  simp only [List.mem_append, Finset.mem_toList, List.mem_cons, List.mem_singleton,
    List.mem_finRange, F, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem source_total {k t : ℕ} (hk : 0 < k) (l : List (Fin k))
    (hp : l.Perm (List.finRange k)) : (l.map (actualSource k t)).sum = 0 := by
  rw [(hp.map (actualSource k t)).sum_eq]
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  exact (ZeroSumSubsets.source_cycle hk t).2.1

private theorem inserted_perm {k : ℕ} (l : List (Fin k)) (j : ℕ)
    (hp : l.Perm (List.finRange k)) :
    (earWord k l j).Perm (List.finRange (k + 1)) := by
  have h : (earWord k l j).Perm (l.map Fin.castSucc ++ [Fin.last k]) := by
    unfold earWord
    have hp' :=
      (List.perm_append_comm (l₁ := [Fin.last k]) (l₂ := (l.drop j).map Fin.castSucc)).append_left
        ((l.take j).map Fin.castSucc)
    have hj : (l.take j).map Fin.castSucc ++
        ((l.drop j).map Fin.castSucc ++ [Fin.last k]) =
        l.map Fin.castSucc ++ [Fin.last k] := by
      rw [← List.append_assoc, ← List.map_append, List.take_append_drop]
    rw [hj] at hp'
    simpa only [List.append_assoc] using hp'
  exact h.trans (by simpa only [List.finRange_succ_last] using
    (hp.map Fin.castSucc).append_right [Fin.last k])

set_option maxHeartbeats 2000000 in
/-- One literal V-mask gives both full actual-source orders at the same zero cut. -/
theorem actualSource_two_negative_joint_lift (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hba : b < a) :
    ∃ sigma : List (Fin (a + b)), ∃ j : ℕ, j ≤ a + b ∧
      OriginalOrder (a + b) (2 ^ a + 1) sigma ∧
      OriginalOrder (a + b + 1) (2 * (2 ^ a + 1))
        (earWord (a + b) sigma j) := by
  classical
  let k := a + b
  let q : ℤ := 2 ^ a
  let r : ℤ := 2 ^ b
  let Q : ℤ := 2 ^ (a - 1)
  let R : ℤ := 2 ^ (b - 1)
  let v : ℕ := 2 ^ a + 1
  let N := modulus k
  let C := N / 2
  let A := 2 * r + 1
  let alpha : Fin k := ⟨b - 1, by dsimp [k]; omega⟩
  let beta : Fin k := ⟨k - 1, by dsimp [k]; omega⟩
  let f := actualSource k v
  let gn := actualSource (k + 1) (2 * v)
  let g := fun i : Fin k => actualSource (k + 1) (2 * v) i.castSucc
  let fresh : Fin (k + 1) := Fin.last k
  have hq : q = 2 * Q := by
    dsimp [q, Q]
    calc
      (2 : ℤ) ^ a = 2 ^ ((a - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ring
  have hr : r = 2 * R := by
    dsimp [r, R]
    calc
      (2 : ℤ) ^ b = 2 ^ ((b - 1) + 1) :=
        congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
      _ = 2 * 2 ^ (b - 1) := by rw [pow_succ]; ring
  have hr4 : 4 ≤ r := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hb
    norm_num at h
    exact h
  have hq2r : 2 * r ≤ q := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
      (show b + 1 ≤ a by omega)
    simpa [q, r, pow_succ, mul_comm] using h
  have hq8 : 8 ≤ q := by omega
  have hqr8 : 8 * r ≤ q * r := mul_le_mul_of_nonneg_right hq8 (by omega)
  have hqr4 : 4 * q ≤ q * r := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hr4 (show 0 ≤ q by omega)
  have hQR : 0 < Q ∧ 0 < R := by dsimp [Q, R]; constructor <;> positivity
  have hvc : (v : ℤ) = q + 1 := by simp [v, q]
  have hN : N = q * r - 1 := by dsimp [N, modulus, k, q, r]; rw [pow_add]
  have hC : C = q * R - 1 := by
    have hn : N = 2 * (q * R) - 1 := by rw [hN, hr]; ring
    dsimp [C]; rw [hn]; omega
  have hC2 : 2 * C = N - 1 := by rw [hC, hN, hr]; ring
  have hNpos : 0 < N := by rw [hN]; nlinarith
  have hNodd : N % 2 = 1 := by
    have hn : N = 2 * (q * R) - 1 := by rw [hN, hr]; ring
    rw [hn]; omega
  have hM : modulus (k + 1) = 2 * N + 1 := by
    dsimp [N, modulus]; rw [pow_succ]; ring
  have hMH : modulus (k + 1) / 2 = N := by rw [hM]; omega
  have hMP : 0 < modulus (k + 1) := by rw [hM]; omega
  have hMO : modulus (k + 1) % 2 = 1 := by rw [hM]; omega
  have hpk : (2 : ℤ) ^ (k - 1) = Q * r := by
    have he : k - 1 = (a - 1) + b := by dsimp [k]; omega
    dsimp [Q, r]; rw [he, pow_add]
  have old_value (i : Fin k) (x m : ℤ) (hx : -C ≤ x ∧ x ≤ C)
      (he : (2 : ℤ) ^ i.val * (v : ℤ) = x + m * N) : f i = x := by
    apply centered_unique hNpos hNodd (centered_bounds hNpos hNodd _) hx
    change centered N _ % N = x % N
    rw [centered_mod, he]
    simp [Int.add_emod, Int.mul_emod]
  have new_value (i : Fin (k + 1)) (x m : ℤ) (hx : -N ≤ x ∧ x ≤ N)
      (he : (2 : ℤ) ^ i.val * ((2 * v : ℕ) : ℤ) =
        x + m * modulus (k + 1)) : actualSource (k + 1) (2 * v) i = x := by
    apply centered_unique hMP hMO (centered_bounds hMP hMO _) (by simpa [hMH] using hx)
    rw [centered_mod, he]
    simp [Int.add_emod, Int.mul_emod]
  have U (i : ℕ) (hi : i < b - 1) :
      f ⟨i, by dsimp [k]; omega⟩ = (q + 1) * 2 ^ i ∧
      g ⟨i, by dsimp [k]; omega⟩ = 2 * (q + 1) * 2 ^ i := by
    have ht : 4 * (2 : ℤ) ^ i ≤ r := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show i + 2 ≤ b by omega)
      simpa [r, pow_add, mul_comm] using h
    have ht0 : 0 < (2 : ℤ) ^ i := by positivity
    have hs0 : 0 ≤ (q + 1) * (2 : ℤ) ^ i := by positivity
    have hs20 : 0 ≤ 2 * (q + 1) * (2 : ℤ) ^ i := by positivity
    have hbnd : 2 * ((q + 1) * (2 : ℤ) ^ i) ≤ N - 1 := by
      have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ q + 1 by nlinarith)
      rw [hN]
      nlinarith
    constructor
    · apply old_value _ _ 0 (by constructor <;> nlinarith)
      simp only [Fin.val_mk, hvc]; ring
    · apply new_value _ _ 0 (by constructor <;> nlinarith)
      simp only [Fin.val_castSucc, Fin.val_mk, Nat.cast_mul, Nat.cast_ofNat, hvc]; ring
  have V (i : ℕ) (hi : i < a - 1) :
      f ⟨b + i, by dsimp [k]; omega⟩ = (r + 1) * 2 ^ i ∧
      g ⟨b + i, by dsimp [k]; omega⟩ = A * 2 ^ i := by
    have ht : 4 * (2 : ℤ) ^ i ≤ q := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
        (show i + 2 ≤ a by omega)
      simpa [q, pow_add, mul_comm] using h
    have ht0 : 0 < (2 : ℤ) ^ i := by positivity
    have hs0 : 0 ≤ (r + 1) * (2 : ℤ) ^ i := by positivity
    have hsA0 : 0 ≤ A * (2 : ℤ) ^ i := by dsimp [A]; positivity
    have hbnd : 2 * ((r + 1) * (2 : ℤ) ^ i) ≤ N - 1 ∧
        A * (2 : ℤ) ^ i ≤ N := by
      have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ r + 1 by omega)
      have hm' := mul_le_mul_of_nonneg_left ht (show 0 ≤ A by dsimp [A]; omega)
      rw [hN]
      dsimp [A] at *
      constructor <;> nlinarith
    constructor
    · apply old_value _ _ ((2 : ℤ) ^ i) (by constructor <;> nlinarith)
      simp only [Fin.val_mk, pow_add, hvc]
      change r * 2 ^ i * (q + 1) = _
      rw [hN]; ring
    · apply new_value _ _ ((2 : ℤ) ^ i) (by dsimp [A] at *; constructor <;> nlinarith)
      simp only [Fin.val_castSucc, Fin.val_mk, pow_add, Nat.cast_mul, Nat.cast_ofNat, hvc]
      change r * 2 ^ i * (2 * (q + 1)) = _
      rw [hM, hN]; dsimp [A]; ring
  have hAlpha : f alpha = -C + R := by
    apply old_value _ _ 1 (by rw [hC]; constructor <;> nlinarith)
    change R * (v : ℤ) = _
    rw [hvc, hC, hN, hr]; ring
  have hBeta : f beta = -C + Q := by
    apply old_value _ _ (Q + 1) (by rw [hC]; constructor <;> nlinarith)
    change (2 : ℤ) ^ (k - 1) * (v : ℤ) = _
    rw [hpk, hvc, hC, hN, hr, hq]; ring
  have hAlphaNew : g alpha = -N + r := by
    apply new_value _ _ 1 (by rw [hN]; constructor <;> nlinarith)
    change R * ((2 * v : ℕ) : ℤ) = _
    rw [Nat.cast_mul, Nat.cast_ofNat, hvc, hM, hN, hr]; ring
  have hBetaNew : g beta = -N + Q := by
    apply new_value _ _ (Q + 1) (by rw [hN]; constructor <;> nlinarith)
    change (2 : ℤ) ^ (k - 1) * ((2 * v : ℕ) : ℤ) = _
    rw [hpk, Nat.cast_mul, Nat.cast_ofNat, hvc, hM, hN, hq]; ring
  have hFresh : gn fresh = (v : ℤ) := by
    apply new_value _ _ (v : ℤ) (by rw [hvc, hN]; constructor <;> nlinarith)
    change (2 : ℤ) ^ k * ((2 * v : ℕ) : ℤ) = _
    have he : (2 : ℤ) ^ k = N + 1 := by dsimp [N, modulus]; ring
    rw [he, Nat.cast_mul, Nat.cast_ofNat, hM]; ring
  let w : ℕ := ((N - (v : ℤ)) / A).toNat
  have hD : 0 ≤ N - (v : ℤ) := by rw [hN, hvc]; nlinarith
  have hA : 0 < A := by dsimp [A]; omega
  have hw : (w : ℤ) = (N - (v : ℤ)) / A := by
    dsimp [w]
    exact Int.toNat_of_nonneg (Int.ediv_nonneg hD (le_of_lt hA))
  have hfloor : A * (w : ℤ) ≤ N - (v : ℤ) ∧
      N - (v : ℤ) < A * ((w : ℤ) + 1) := by
    have h := Int.emod_add_mul_ediv (N - (v : ℤ)) A
    have hlo := Int.emod_nonneg (N - (v : ℤ)) (ne_of_gt hA)
    have hhi := Int.emod_lt_of_pos (N - (v : ℤ)) hA
    rw [← hw] at h
    constructor <;> nlinarith
  have hwQ : (w : ℤ) < Q := by
    have hh : N - (v : ℤ) < A * Q := by rw [hN, hvc, hq]; dsimp [A]; nlinarith
    exact (Int.mul_lt_mul_left hA).mp (lt_of_le_of_lt hfloor.1 hh)
  have hwbits : w < 2 ^ (a - 1) := by
    exact_mod_cast (show (w:ℤ) < (2:ℤ) ^ (a-1) from hwQ)
  let mask := DyadicPrefix.bitSubset (a - 1) w hwbits
  let label : Fin (a - 1) → Fin k := fun i => ⟨b + i.val, by dsimp [k]; omega⟩
  have hinj : Function.Injective label := by
    intro i j hij; apply Fin.ext
    have h := congrArg Fin.val hij
    dsimp [label] at h; omega
  let ES := mask.image label
  let FS := Finset.univ \ (ES ∪ {alpha,beta})
  let E := ES.toList
  let F := FS.toList
  have E_values (i : Fin k) (hi : i ∈ ES) :
      ∃ j : Fin (a - 1), i = label j ∧ j ∈ mask := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨j, rfl, hj⟩
  have hEa : alpha ∉ ES := by
    intro hi
    obtain ⟨j, hj, _⟩ := E_values alpha hi
    have h := congrArg Fin.val hj
    dsimp [alpha, label] at h; omega
  have hEb : beta ∉ ES := by
    intro hi
    obtain ⟨j, hj, _⟩ := E_values beta hi
    have h := congrArg Fin.val hj
    dsimp [beta, label, k] at h; omega
  have hab : alpha ≠ beta := by
    intro h
    have he := congrArg Fin.val h
    dsimp [alpha, beta, k] at he; omega
  have hperm : (E ++ F ++ [alpha,beta]).Perm (List.finRange k) :=
    split_perm ES alpha beta hab hEa hEb
  have hmask : (∑ i ∈ mask, (2 : ℤ) ^ i.val) = (w : ℤ) := by
    exact_mod_cast DyadicPrefix.bit_subset_sum hwbits
  have hEold : (E.map f).sum = (r + 1) * w := by
    rw [← List.sum_toFinset _ ES.nodup_toList, Finset.toList_toFinset]
    change (∑ i ∈ mask.image label, f i) = _
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
    simp_rw [show ∀ i : Fin (a - 1), f (label i) = (r + 1) * 2 ^ i.val from
      fun i => (V i.val i.isLt).1]
    rw [← Finset.mul_sum, hmask]
  have hEnew : (E.map g).sum = A * w := by
    rw [← List.sum_toFinset _ ES.nodup_toList, Finset.toList_toFinset]
    change (∑ i ∈ mask.image label, g i) = _
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
    simp_rw [show ∀ i : Fin (a - 1), g (label i) = A * 2 ^ i.val from
      fun i => (V i.val i.isLt).2]
    rw [← Finset.mul_sum, hmask]
  have pos (i : Fin k) (hi : i ≠ alpha ∧ i ≠ beta) : 0 ≤ f i ∧ 0 ≤ g i := by
    by_cases hu : i.val < b - 1
    · have hv := U i.val hu
      have he : i = ⟨i.val, by dsimp [k]; omega⟩ := Fin.ext rfl
      rw [he, hv.1, hv.2]
      constructor <;> positivity
    · have hai : i.val ≠ b - 1 := fun h => hi.1 (Fin.ext h)
      have hbi : i.val ≠ k - 1 := fun h => hi.2 (Fin.ext h)
      have hlt : i.val - b < a - 1 := by dsimp [k] at *; omega
      have he : i = label ⟨i.val - b, hlt⟩ := Fin.ext (by dsimp [label]; omega)
      rw [he, (V _ hlt).1, (V _ hlt).2]
      dsimp [A]
      constructor <;> positivity
  have Epos : ∀ i ∈ E, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    apply pos i
    have hm : i ∈ ES := Finset.mem_toList.mp hi
    exact ⟨fun h => hEa (h ▸ hm), fun h => hEb (h ▸ hm)⟩
  have Fpos : ∀ i ∈ F, 0 ≤ f i ∧ 0 ≤ g i := by
    intro i hi
    have hm := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hi)).2
    apply pos i
    constructor <;> intro h <;> apply hm <;> simp [h]
  let EN := E.map Fin.castSucc
  let FN := F.map Fin.castSucc
  have ENpos : ∀ i ∈ EN, 0 ≤ gn i := by
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact (Epos j hj).2
  have FNpos : ∀ i ∈ FN, 0 ≤ gn i := by
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact (Fpos j hj).2
  have hEN : (EN.map gn).sum = A * w := by
    change ((E.map Fin.castSucc).map gn).sum = A * w
    rw [List.map_map]
    change (E.map g).sum = A * w
    exact hEnew
  have hOldZero := source_total (t := v) (show 0 < k by dsimp [k]; omega) _ hperm
  have hOldMass : (F.map f).sum = 2 * C - R - Q - (r + 1) * w := by
    change ((E ++ F ++ [alpha,beta]).map f).sum = 0 at hOldZero
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hEold, hAlpha, hBeta] at hOldZero
    linarith
  have hNewPerm : (EN ++ FN ++ [alpha.castSucc,beta.castSucc,fresh]).Perm
      (List.finRange (k + 1)) := by
    have hp := (hperm.map Fin.castSucc).append_right [fresh]
    simpa [EN, FN, List.map_append, List.finRange_succ_last, fresh, List.append_assoc] using hp
  have hNewZero := source_total (t := 2 * v) (show 0 < k + 1 by omega) _ hNewPerm
  have hNewMass : (FN.map gn).sum = 2 * N - r - Q - (v : ℤ) - A * w := by
    change ((EN ++ FN ++ [alpha.castSucc,beta.castSucc,fresh]).map gn).sum = 0 at hNewZero
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hEN] at hNewZero
    change A * w + (FN.map gn).sum + (g alpha + (g beta + (gn fresh + 0))) = 0 at hNewZero
    rw [hAlphaNew, hBetaNew, hFresh] at hNewZero
    linarith
  let p : ℤ := (r + 1) * w
  let z : ℤ := A * w
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hz0 : 0 ≤ z := by dsimp [z, A]; positivity
  have finish (sigma : List (Fin k)) (j : ℕ) (hj : j ≤ k)
      (hp : sigma.Perm (List.finRange k)) (hs : InStrip f C 0 sigma)
      (hn : InStrip gn N 0 (earWord k sigma j)) :
      ∃ sigma : List (Fin (a + b)), ∃ j : ℕ, j ≤ a + b ∧
        OriginalOrder (a + b) (2 ^ a + 1) sigma ∧
        OriginalOrder (a + b + 1) (2 * (2 ^ a + 1)) (earWord (a + b) sigma j) := by
    change ∃ sigma : List (Fin k), ∃ j : ℕ, j ≤ k ∧
      OriginalOrder k v sigma ∧ OriginalOrder (k + 1) (2 * v) (earWord k sigma j)
    have hk : 0 < k := by dsimp [k]; omega
    have hnp := inserted_perm sigma j hp
    refine ⟨sigma,j,hj,⟨hp,source_total hk _ hp,?_⟩,
      ⟨hnp,source_total (by omega) _ hnp,?_⟩⟩
    · intro n
      change 0 ≤ ((sigma.take n).map f).sum ∧ ((sigma.take n).map f).sum ≤ C
      simpa only [zero_add] using inStrip_prefix hs n
    · intro n
      change 0 ≤ (((earWord k sigma j).take n).map gn).sum ∧
        (((earWord k sigma j).take n).map gn).sum ≤ modulus (k + 1) / 2
      rw [hMH]
      simpa only [zero_add] using inStrip_prefix hn n
  by_cases h2 : a = b + 1
  · have hqr : q = 2 * r := by dsimp [q,r]; rw [h2,pow_succ]; ring
    have hw2 : (w : ℤ) = r - 2 := by
      obtain ⟨hl,hu⟩ := hfloor
      rw [hN,hvc,hqr] at hl hu
      dsimp [A] at hl hu
      have hlo : r - 2 ≤ (w : ℤ) := by
        by_contra h
        have hm := mul_le_mul_of_nonneg_left (show (w : ℤ) + 1 ≤ r - 2 by omega)
          (show 0 ≤ 2*r+1 by omega)
        nlinarith only [hu, hm]
      have hhi : (w : ℤ) < r - 1 := by
        by_contra h
        have hm := mul_le_mul_of_nonneg_left (show r - 1 ≤ (w : ℤ) by omega)
          (show 0 ≤ 2*r+1 by omega)
        nlinarith only [hl, hm]
      omega
    have hQeq : Q = r := by omega
    have hp2 : p = C - Q - 1 := by
      dsimp [p]; rw [hw2,hC,hqr,hQeq,hr]; ring
    have hz2 : z + (v : ℤ) = N - r := by
      dsimp [z,A]; rw [hw2,hvc,hN,hqr]; ring
    let sigma := F ++ [alpha] ++ E ++ [beta]
    have hsperm : sigma.Perm (List.finRange k) := by
      have hswap : sigma.Perm (F ++ E ++ [alpha,beta]) := by
        simpa only [sigma, List.append_assoc, List.cons_append, List.nil_append] using
          ((List.perm_append_comm (l₁ := [alpha]) (l₂ := E)).append_right [beta]).append_left F
      exact hswap.trans
        (((List.perm_append_comm (l₁ := F) (l₂ := E)).append_right [alpha,beta]).trans hperm)
    have hlen : (F ++ [alpha] ++ E).length = k - 1 := by
      have hh := hsperm.length_eq
      simp only [sigma,List.length_append,List.length_cons,List.length_nil,List.length_finRange] at hh ⊢
      omega
    have hear : earWord k sigma (k - 1) = FN ++ [alpha.castSucc] ++ EN ++ [fresh,beta.castSucc] := by
      rw [← hlen]
      change earWord k ((F ++ [alpha] ++ E) ++ [beta]) (F ++ [alpha] ++ E).length = _
      unfold earWord
      rw [List.take_left, List.drop_left]
      simp only [EN, FN, fresh, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append]
    have hs : InStrip f C 0 sigma := by
      apply two_blocks f C F E alpha beta (fun i hi => (Fpos i hi).1)
        (fun i hi => (Epos i hi).1)
      · rw [hOldMass,hAlpha,hBeta,hEold]; ring
      · rw [hOldMass]; change 0 ≤ 2*C-R-Q-p ∧ 2*C-R-Q-p ≤ C
        rw [hp2]; omega
      · rw [hOldMass,hAlpha]; change 0 ≤ 2*C-R-Q-p+(-C+R)
        rw [hp2]; omega
      · rw [hBeta]; omega
    have hn : InStrip gn N 0 (earWord k sigma (k - 1)) := by
      rw [hear]
      have hns : InStrip gn N 0 (FN ++ [alpha.castSucc] ++ (EN ++ [fresh]) ++ [beta.castSucc]) := by
        apply two_blocks gn N FN (EN ++ [fresh]) alpha.castSucc beta.castSucc FNpos
          (by intro i hi; rcases List.mem_append.mp hi with hi|hi
              · exact ENpos i hi
              · have he := List.mem_singleton.mp hi
                subst i
                rw [hFresh]
                omega)
        · simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
          change (FN.map gn).sum + g alpha + ((EN.map gn).sum + gn fresh) + g beta = 0
          rw [hNewMass,hEN,hAlphaNew,hBetaNew,hFresh]; ring
        · rw [hNewMass]; change 0 ≤ 2*N-r-Q-(v:ℤ)-z ∧ 2*N-r-Q-(v:ℤ)-z ≤ N
          omega
        · change 0 ≤ (FN.map gn).sum + g alpha
          rw [hNewMass,hAlphaNew]; change 0 ≤ 2*N-r-Q-(v:ℤ)-z+(-N+r)
          omega
        · change 0 ≤ -g beta ∧ -g beta ≤ N
          rw [hBetaNew]; omega
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hns
    exact finish sigma (k-1) (by omega) hsperm hs hn
  · have h4 : b + 2 ≤ a := by omega
    have bounds : C - Q ≤ p ∧ p ≤ C ∧ N - Q ≤ z + (v : ℤ) ∧ z + (v : ℤ) ≤ N := by
      by_cases h4eq : a = b + 2
      · have hqr : q = 4 * r := by dsimp [q,r]; rw [h4eq,pow_add]; norm_num; ring
        have hw4 : (w : ℤ) = 2*r-3 := by
          obtain ⟨hl,hu⟩ := hfloor
          rw [hN,hvc,hqr] at hl hu
          dsimp [A] at hl hu
          have hlo : 2*r-3 ≤ (w:ℤ) := by
            by_contra h
            have hm := mul_le_mul_of_nonneg_left (show (w:ℤ)+1 ≤ 2*r-3 by omega)
              (show 0 ≤ 2*r+1 by omega)
            nlinarith only [hu, hm]
          have hhi : (w:ℤ) < 2*r-2 := by
            by_contra h
            have hm := mul_le_mul_of_nonneg_left (show 2*r-2 ≤ (w:ℤ) by omega)
              (show 0 ≤ 2*r+1 by omega)
            nlinarith only [hl, hm, hr4]
          omega
        have hQeq : Q = 2*r := by omega
        have hp4 : p - (C-Q) = r-2 := by
          dsimp [p]; rw [hw4,hC,hqr,hQeq,hr]; ring
        have hp4u : C-p = r+2 := by
          dsimp [p]; rw [hw4,hC,hqr,hr]; ring
        have hz4 : z + (v:ℤ) = N-1 := by
          dsimp [z,A]; rw [hw4,hvc,hN,hqr]; ring
        refine ⟨by omega,by omega,by omega,by omega⟩
      · have h8 : 8*r ≤ q := by
          have h := pow_le_pow_right₀ (by norm_num : (1:ℤ) ≤ 2)
            (show b+3 ≤ a by omega)
          simpa [q,r,pow_add,mul_comm] using h
        have hzl : N-q-2*r-1 ≤ z := by
          have hh := hfloor.2
          have he : A * ((w:ℤ)+1) = z+A := by dsimp [z]; ring
          rw [he,hvc] at hh
          dsimp [A] at hh
          omega
        have hzu : z ≤ N-q-1 := by have hh := hfloor.1; rw [hvc] at hh; omega
        have margin : 0 ≤ q*(r-1)-4*r^2-4*r-2 := by
          nlinarith only [hr4,
            mul_nonneg (show 0 ≤ q-8*r by omega) (show 0 ≤ r-1 by omega),
            mul_nonneg (show 0 ≤ r-4 by omega) (show 0 ≤ 4*r+4 by omega)]
        have hidlo : 2*(r+1)*(N-q-2*r-1)-(2*C-q)*A = q*(r-1)-4*r^2-4*r-2 := by
          rw [show 2*C-q = N-1-q by omega,hN]; dsimp [A]; ring
        have hidhi : (2*C)*A-2*(r+1)*(N-q-1) = q*(r+2)+2 := by
          rw [hC2,hN]; dsimp [A]; ring
        have hmlo := mul_le_mul_of_nonneg_left hzl (show 0 ≤ 2*(r+1) by omega)
        have hmhi := mul_le_mul_of_nonneg_left hzu (show 0 ≤ 2*(r+1) by omega)
        have hrel : 2*(r+1)*z = 2*p*A := by dsimp [p,z]; ring
        refine ⟨?_,?_,?_,?_⟩
        · apply (Int.mul_le_mul_right (show 0 < 2*A by omega)).mp
          rw [hq] at hidlo hmlo margin
          nlinarith only [hidlo, hmlo, margin, hrel]
        · apply (Int.mul_le_mul_right (show 0 < 2*A by omega)).mp
          nlinarith only [hidhi, hmhi, hrel, hq8, hr4]
        · omega
        · exact (by have hh := hfloor.1; dsimp [z] at *; omega)
    obtain ⟨hpl,hpu,hzl,hzu⟩ := bounds
    let sigma := E ++ [beta] ++ F ++ [alpha]
    have hsperm : sigma.Perm (List.finRange k) := by
      have hswap : sigma.Perm (E ++ F ++ [beta,alpha]) := by
        simpa only [sigma, List.append_assoc, List.cons_append, List.nil_append] using
          ((List.perm_append_comm (l₁ := [beta]) (l₂ := F)).append_right [alpha]).append_left E
      exact hswap.trans (((List.Perm.swap alpha beta []).append_left (E ++ F)).trans hperm)
    have hear : earWord k sigma E.length = EN ++ [fresh,beta.castSucc] ++ FN ++ [alpha.castSucc] := by
      rw [show sigma = E ++ ([beta] ++ F ++ [alpha]) by
        simp only [sigma, List.append_assoc]]
      unfold earWord
      rw [List.take_left, List.drop_left]
      simp only [EN, FN, fresh, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append]
    have hs : InStrip f C 0 sigma := by
      apply two_blocks f C E F beta alpha (fun i hi => (Epos i hi).1)
        (fun i hi => (Fpos i hi).1)
      · rw [hOldMass,hAlpha,hBeta,hEold]; ring
      · rw [hEold]; exact ⟨hp0, hpu⟩
      · rw [hEold,hBeta]; change 0 ≤ p+(-C+Q); omega
      · rw [hAlpha]; omega
    have hn : InStrip gn N 0 (earWord k sigma E.length) := by
      rw [hear]
      have hns : InStrip gn N 0 ((EN ++ [fresh]) ++ [beta.castSucc] ++ FN ++ [alpha.castSucc]) := by
        apply two_blocks gn N (EN ++ [fresh]) FN beta.castSucc alpha.castSucc
          (by intro i hi; rcases List.mem_append.mp hi with hi|hi
              · exact ENpos i hi
              · have he := List.mem_singleton.mp hi; subst i; rw [hFresh]; omega) FNpos
        · simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
          change ((EN.map gn).sum + gn fresh) + g beta + (FN.map gn).sum + g alpha = 0
          rw [hNewMass,hEN,hAlphaNew,hBetaNew,hFresh]; ring
        · simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
          rw [hEN,hFresh]; change 0 ≤ z+(v:ℤ) ∧ z+(v:ℤ) ≤ N
          omega
        · simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
          change 0 ≤ ((EN.map gn).sum + gn fresh) + g beta
          rw [hEN,hFresh,hBetaNew]; change 0 ≤ z+(v:ℤ)+(-N+Q); omega
        · change 0 ≤ -g alpha ∧ -g alpha ≤ N
          rw [hAlphaNew]; omega
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hns
    have hj : E.length ≤ k := by
      have hh := hsperm.length_eq
      simp only [sigma,List.length_append,List.length_cons,List.length_nil,List.length_finRange] at hh
      omega
    exact finish sigma E.length hj hsperm hs hn

#print axioms actualSource_two_negative_joint_lift

end D5.S3.Combinatorics.Circle.TwoNegativeJointLift
