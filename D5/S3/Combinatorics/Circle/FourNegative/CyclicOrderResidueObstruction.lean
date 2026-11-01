/- GID: D5/S3/Combinatorics/Circle/FourNegative/CyclicOrderResidueObstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/CyclicOrderResidueObstruction
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Unbounded physical cyclic-order obstruction from dyadic residues modulo 85. -/
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source
import Batteries.Tactic.OpenPrivate

/-! Two prescribed physical negative orders are incompatible with a literal joint ear
for gaps (2,2,2,n) when eight divides n. Other negative orders remain in scope. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.CyclicOrderResidueObstruction
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private chains last_double from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source
open private ear_prefix ear_perm from D5.S3.Combinatorics.Circle.RunFirstEarTransport
open private sum_linear from D5.S3.Combinatorics.Circle.PeriodicShortening

private theorem dyadic_residue (n : ℕ) (hn : n % 8 = 0) :
    (2 : ℤ) ^ n % 85 = 1 := by
  obtain ⟨t, rfl⟩ := Nat.dvd_of_mod_eq_zero hn
  rw [pow_mul]
  have h : (2 : ℤ) ^ 8 ≡ 1 [ZMOD 85] := by norm_num [Int.ModEq]
  simpa [Int.ModEq] using Int.ModEq.pow t h

private theorem residue_windows (x m H K : ℤ) (v w z e : Bool)
    (hx : 4 ≤ x) (hr : x % 85 = 1) (hm : 2 * m ≤ x - 2)
    (hH : 0 ≤ H ∧ H ≤ 42) (hK : 0 ≤ K ∧ K ≤ 42)
    (order : Bool)
    (hheight : H = 85 * m -
      ((if order then 78 else 56) - 21 * (if v then 1 else 0) -
        20 * (if w then 1 else 0) - 16 * (if z then 1 else 0)) * x +
      ((if order then 57 else 54) + (if v then 1 else 0) +
        5 * (if w then 1 else 0) + 21 * (if z then 1 else 0)))
    (hcharge : K = 2 * H - ((if order then 57 else 54) +
      (if v then 1 else 0) + 5 * (if w then 1 else 0) +
      21 * (if z then 1 else 0)) + 85 * (if e then 1 else 0)) : False := by
  cases order <;> cases v <;> cases w <;> cases z <;> cases e <;>
    norm_num at hheight hcharge <;> omega

private theorem source_chains (n : ℕ) (hn : 2 ≤ n) :
    let x : ℤ := 2 ^ n
    let f := fun i : ℕ => centered (modulus (n + 6)) ((2 : ℤ) ^ i * 85)
    let g := fun i : ℕ => centered (modulus (n + 7)) ((2 : ℤ) ^ i * 170)
    (∀ i, i + 1 < n → f i = 85 * 2 ^ i ∧ g i = 170 * 2 ^ i) ∧
    (2 * f (n - 1) = 2 - 43 * x ∧ g (n - 1) = 1 - 43 * x) ∧
    (f n = 21 * x + 1 ∧ g n = 42 * x + 1) ∧
    (f (n + 1) = 3 - 22 * x ∧ g (n + 1) = 3 - 44 * x) ∧
    (f (n + 2) = 20 * x + 5 ∧ g (n + 2) = 40 * x + 5) ∧
    (f (n + 3) = 11 - 24 * x ∧ g (n + 3) = 11 - 48 * x) ∧
    (f (n + 4) = 16 * x + 21 ∧ g (n + 4) = 32 * x + 21) ∧
    (f (n + 5) = 43 - 32 * x ∧ g (n + 5) = 43 - 64 * x) ∧
    g (n + 6) = 85 := by
  dsimp only
  let x : ℤ := 2 ^ n
  let N := modulus (n + 6)
  let M := modulus (n + 7)
  let f := fun i : ℕ => centered N ((2 : ℤ) ^ i * 85)
  let F := fun i : ℕ => centered M ((2 : ℤ) ^ i * 85)
  let g := fun i : ℕ => centered M ((2 : ℤ) ^ i * 170)
  have hN : N = 64 * x - 1 := by dsimp [N, modulus, x]; rw [pow_add]; norm_num; ring
  have hM : M = 128 * x - 1 := by dsimp [M, modulus, x]; rw [pow_add]; norm_num; ring
  have h2 := chains 2 2 2 n (by decide) (by decide) (by decide) hn
  have h3 := chains 2 2 2 (n + 1) (by decide) (by decide) (by decide) (by omega)
  norm_num only [show (2 : ℤ) ^ 2 = 4 by norm_num] at h2 h3
  obtain ⟨_, hU, hV, hW, hX⟩ := h2
  obtain ⟨_, hUn, hVn, hWn, hXn⟩ := h3
  have nk : 2 + 2 + 2 + n = n + 6 := by omega
  have nkn : 2 + 2 + 2 + (n + 1) = n + 7 := by omega
  rw [nk] at hU hV hW hX
  rw [nkn] at hUn hVn hWn hXn
  have hshift (i : ℕ) : g i = F (i + 1) := by
    dsimp [g, F]; rw [pow_succ]; congr 1; ring
  change (∀ i, i + 1 < n → f i = 85 * 2 ^ i ∧ g i = 170 * 2 ^ i) ∧ _
  constructor
  · intro i hi
    constructor
    · simpa [f, N, hi, mul_comm] using hU i (by omega)
    · rw [hshift]
      have hh := hUn (i + 1) (by omega)
      have he : F (i + 1) = (2 : ℤ) ^ (i + 1) * 85 := by
        simpa [F, M, show i + 1 + 1 < n + 1 by omega] using hh
      rw [he, pow_succ]
      ring
  · have hpow : (2 : ℤ) ^ (n + 1) = 2 * x := by dsimp [x]; rw [pow_succ]; ring
    have u := hU (n - 1) (by omega)
    have un := hUn n (by omega)
    have v := hV 0 (by decide)
    have vn := hVn 0 (by decide)
    have nv := hV 1 (by decide)
    have nvn := hVn 1 (by decide)
    have w := hW 0 (by decide)
    have wn := hWn 0 (by decide)
    have nw := hW 1 (by decide)
    have nwn := hWn 1 (by decide)
    have z := hX 0 (by decide)
    have zn := hXn 0 (by decide)
    have nz := hX 1 (by decide)
    have nzn := hXn 1 (by decide)
    simp only [show ¬ n - 1 + 1 < n by omega, show ¬ n + 1 < n + 1 by omega,
      ite_false] at u un
    norm_num only [pow_zero, pow_one, zero_add, add_zero, show 0 + 1 < 2 by decide,
      show ¬ 1 + 1 < 2 by decide, ite_true, ite_false, one_mul]
        at v vn nv nvn w wn nw nwn z zn nz nzn
    change f (n - 1) = _ at u
    change F n = _ at un
    have gnu : g (n - 1) = F n := by rw [hshift, show n - 1 + 1 = n by omega]
    have hx : 4 ≤ x := by
      dsimp [x]
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hn
    have hxe : x = 2 * (2 : ℤ) ^ (n - 1) := by
      dsimp [x]
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      ring
    have fresh : g (n + 6) = 85 := by
      rw [hshift]
      change centered M ((2 : ℤ) ^ (n + 7) * 85) = 85
      have hperiod := centered_full_period (n + 7) 85
      norm_num only [Nat.cast_ofNat] at hperiod
      rw [show M = modulus (n + 7) from rfl, hperiod]
      change centered M 85 = 85
      dsimp only [centered]
      rw [hM]
      have hhalf : (128 * x - 1) / 2 = 64 * x - 1 := by omega
      rw [hhalf, Int.emod_eq_of_lt (by omega) (by omega)]
      ring
    have hu : 2 * f (n - 1) = 2 - 43 * x := by
      change f (n - 1) = -(N - (1 + x + x * 4 + x * 4 * 4)) / 2 at u
      rw [hN] at u
      omega
    have hun : g (n - 1) = 1 - 43 * x := by
      rw [gnu]
      change F n = -(M - (1 + 2 ^ (n + 1) + 2 ^ (n + 1) * 4 + 2 ^ (n + 1) * 4 * 4)) / 2 at un
      rw [hM, hpow] at un
      omega
    have hv : f n = 21 * x + 1 := by
      change f n = 1 + x + x * 4 + x * 4 * 4 at v
      linarith only [v]
    have hvn : g n = 42 * x + 1 := by
      rw [hshift]
      change F (n + 1) = 1 + 2 ^ (n + 1) + 2 ^ (n + 1) * 4 + 2 ^ (n + 1) * 4 * 4 at vn
      rw [hpow] at vn
      linarith only [vn]
    have hnv : f (n + 1) = 3 - 22 * x := by
      change f (n + 1) = -(N - (1 + 4 + 4 * x + 4 * x * 4)) / 2 at nv
      rw [hN] at nv
      omega
    have hnvn : g (n + 1) = 3 - 44 * x := by
      rw [hshift]
      change F (n + 1 + 1) = -(M - (1 + 4 + 4 * 2 ^ (n + 1) + 4 * 2 ^ (n + 1) * 4)) / 2 at nvn
      rw [hM, hpow] at nvn
      omega
    have hw : f (n + 2) = 20 * x + 5 := by
      change f (n + 2) = 1 + 4 + 4 * x + 4 * x * 4 at w
      linarith only [w]
    have hwn : g (n + 2) = 40 * x + 5 := by
      rw [hshift]
      change F (n + 1 + 2) = 1 + 4 + 4 * 2 ^ (n + 1) + 4 * 2 ^ (n + 1) * 4 at wn
      rw [hpow] at wn
      have he : n + 1 + 2 = n + 2 + 1 := by omega
      rw [he] at wn
      linarith only [wn]
    have hnw : f (n + 3) = 11 - 24 * x := by
      change f (n + 2 + 1) = -(N - (1 + 4 + 4 * 4 + 4 * 4 * x)) / 2 at nw
      rw [hN] at nw
      have he : n + 2 + 1 = n + 3 := by omega
      rw [he] at nw
      omega
    have hnwn : g (n + 3) = 11 - 48 * x := by
      rw [hshift]
      change F (n + 1 + 2 + 1) = -(M - (1 + 4 + 4 * 4 + 4 * 4 * 2 ^ (n + 1))) / 2 at nwn
      rw [hM, hpow] at nwn
      have he : n + 1 + 2 + 1 = n + 3 + 1 := by omega
      rw [he] at nwn
      omega
    have hz : f (n + 4) = 16 * x + 21 := by
      change f (n + 4) = 1 + 4 + 4 * 4 + 4 * 4 * x at z
      linarith only [z]
    have hzn : g (n + 4) = 32 * x + 21 := by
      rw [hshift]
      change F (n + 1 + 2 + 2) = 1 + 4 + 4 * 4 + 4 * 4 * 2 ^ (n + 1) at zn
      rw [hpow] at zn
      have he : n + 1 + 2 + 2 = n + 4 + 1 := by omega
      rw [he] at zn
      linarith only [zn]
    have hnz : f (n + 5) = 43 - 32 * x := by
      change f (n + 2 + 2 + 1) = -(N - 85) / 2 at nz
      rw [hN] at nz
      have he : n + 2 + 2 + 1 = n + 5 := by omega
      rw [he] at nz
      omega
    have hnzn : g (n + 5) = 43 - 64 * x := by
      rw [hshift]
      change F (n + 1 + 2 + 2 + 1) = -(M - 85) / 2 at nzn
      rw [hM] at nzn
      have he : n + 1 + 2 + 2 + 1 = n + 5 + 1 := by omega
      rw [he] at nzn
      omega
    exact ⟨⟨hu, hun⟩, ⟨hv, hvn⟩, ⟨hnv, hnvn⟩, ⟨hw, hwn⟩,
      ⟨hnw, hnwn⟩, ⟨hz, hzn⟩, ⟨hnz, hnzn⟩, fresh⟩

private def uWeight (n i : ℕ) : ℤ := if i + 1 < n then 2 ^ i else 0
private def hit (j i : ℕ) : ℤ := if i = j then 1 else 0

private theorem source_readout (n : ℕ) (hn : 2 ≤ n) (i : ℕ) (hi : i < n + 6) :
    let x : ℤ := 2 ^ n
    let f := centered (modulus (n + 6)) ((2 : ℤ) ^ i * 85)
    let g := centered (modulus (n + 7)) ((2 : ℤ) ^ i * 170)
    2 * f = 170 * uWeight n i + (2 - 43 * x) * hit (n - 1) i +
      (42 * x + 2) * hit n i + (6 - 44 * x) * hit (n + 1) i +
      (40 * x + 10) * hit (n + 2) i + (22 - 48 * x) * hit (n + 3) i +
      (32 * x + 42) * hit (n + 4) i + (86 - 64 * x) * hit (n + 5) i ∧
    2 * f - g = hit (n - 1) i + hit n i + 3 * hit (n + 1) i +
      5 * hit (n + 2) i + 11 * hit (n + 3) i + 21 * hit (n + 4) i +
      43 * hit (n + 5) i := by
  obtain ⟨hU, hnu, hv, hnv, hw, hnw, hz, hnz, _⟩ := source_chains n hn
  dsimp only at hU hnu hv hnv hw hnw hz hnz
  dsimp only
  have hc : i + 1 < n ∨ i = n - 1 ∨ i = n ∨ i = n + 1 ∨ i = n + 2 ∨
      i = n + 3 ∨ i = n + 4 ∨ i = n + 5 := by omega
  rcases hc with hc | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hf, hg⟩ := hU i hc
    rw [hf, hg]
    constructor <;>
      simp [uWeight, hit, hc, show i ≠ n - 1 by omega, show i ≠ n by omega,
      show i ≠ n + 1 by omega, show i ≠ n + 2 by omega, show i ≠ n + 3 by omega,
      show i ≠ n + 4 by omega, show i ≠ n + 5 by omega] <;> ring
  all_goals simp (disch := omega) [uWeight, hit]
  all_goals omega

private theorem hit_sum (S : Finset ℕ) (j : ℕ) :
    (∑ i ∈ S, hit j i) = if j ∈ S then 1 else 0 := by
  classical
  simp [hit]

private theorem u_mass (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ) :
    0 ≤ ∑ i ∈ S, uWeight n i ∧
      2 * (∑ i ∈ S, uWeight n i) ≤ (2 : ℤ) ^ n - 2 := by
  classical
  have hsum (t : ℕ) : (∑ i ∈ Finset.range t, (2 : ℤ) ^ i) = 2 ^ t - 1 := by
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  have hsub : S.filter (fun i => i + 1 < n) ⊆ Finset.range (n - 1) := by
    intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_range]
    omega
  have hb := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => (2 : ℤ) ^ i)
    hsub (by intro i _ _; positivity)
  rw [hsum, Finset.sum_filter] at hb
  change (∑ i ∈ S, uWeight n i) ≤ 2 ^ (n - 1) - 1 at hb
  have hp : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring
  refine ⟨Finset.sum_nonneg (fun i _ => ?_), by omega⟩
  dsimp [uWeight]
  split_ifs <;> positivity

private theorem sublist_positions (s : List ℕ) (hnd : s.Nodup) (l : List ℕ)
    (hl : l.Sublist s) : l.Pairwise (fun a b => s.idxOf a < s.idxOf b) := by
  apply List.Pairwise.sublist hl
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa only [hnd.idxOf_getElem i hi, hnd.idxOf_getElem j hj] using hij

private theorem subset_readout (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < n + 6) :
    let x : ℤ := 2 ^ n
    let F := ∑ i ∈ S, centered (modulus (n + 6)) ((2 : ℤ) ^ i * 85)
    let G := ∑ i ∈ S, centered (modulus (n + 7)) ((2 : ℤ) ^ i * 170)
    let b := fun j => if j ∈ S then (1 : ℤ) else 0
    2 * F = 170 * (∑ i ∈ S, uWeight n i) + (2 - 43 * x) * b (n - 1) +
      (42 * x + 2) * b n + (6 - 44 * x) * b (n + 1) +
      (40 * x + 10) * b (n + 2) + (22 - 48 * x) * b (n + 3) +
      (32 * x + 42) * b (n + 4) + (86 - 64 * x) * b (n + 5) ∧
    2 * F - G = b (n - 1) + b n + 3 * b (n + 1) +
      5 * b (n + 2) + 11 * b (n + 3) + 21 * b (n + 4) + 43 * b (n + 5) := by
  classical
  dsimp only
  constructor
  · have h := Finset.sum_congr rfl (fun i hi => (source_readout n hn i (hS i hi)).1)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, hit_sum] using h
  · have h := Finset.sum_congr rfl (fun i hi => (source_readout n hn i (hS i hi)).2)
    simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hit_sum] using h

/-- No literal joint ear has either of the two specified physical negative orders.
The sublists leave every positive interleaving unrestricted. -/
theorem actual_source_cyclic_order_residue_obstruction
    (n : ℕ) (hn : 2 ≤ n) (h8 : n % 8 = 0)
    (sigma : List (Fin (n + 6))) (cut : ℕ) (hcut : cut ≤ n + 6)
    (hold : OriginalOrder (n + 6) 85 sigma)
    (hnew : OriginalOrder (n + 6 + 1) 170 (earWord (n + 6) sigma cut)) :
    ¬ ([n + 1, n + 3, n + 5, n - 1].Sublist (sigma.map Fin.val) ∨
      [n + 3, n + 5, n - 1, n + 1].Sublist (sigma.map Fin.val)) := by
  classical
  intro hord
  let x : ℤ := 2 ^ n
  let f := fun i : ℕ => centered (modulus (n + 6)) ((2 : ℤ) ^ i * 85)
  let g := fun i : ℕ => centered (modulus (n + 7)) ((2 : ℤ) ^ i * 170)
  let s := sigma.map Fin.val
  have hlen : sigma.length = n + 6 := by simpa using hold.1.length_eq
  have hslen : s.length = n + 6 := by simpa [s] using hlen
  have hnd : s.Nodup := (hold.1.nodup_iff.mpr (List.nodup_finRange _)).map Fin.val_injective
  have memall (i : ℕ) (hi : i < n + 6) : i ∈ s := by
    exact List.mem_map.mpr ⟨⟨i, hi⟩, hold.1.mem_iff.mpr (List.mem_finRange _), rfl⟩
  have membound (i : ℕ) (hi : i ∈ s) : i < n + 6 := by
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hi
    exact a.isLt
  have hx : 4 ≤ x := by
    dsimp [x]
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hn
  have hN : modulus (n + 6) / 2 = 32 * x - 1 := by
    have he : modulus (n + 6) = 64 * x - 1 := by
      dsimp [modulus, x]; rw [pow_add]; norm_num; ring
    rw [he]; omega
  have hM : modulus (n + 7) / 2 = 64 * x - 1 := by
    have he : modulus (n + 7) = 128 * x - 1 := by
      dsimp [modulus, x]; rw [pow_add]; norm_num; ring
    rw [he]; omega
  obtain ⟨_, _, _, _, _, _, _, hX, hfresh⟩ := source_chains n hn
  change f (n + 5) = 43 - 32 * x ∧ g (n + 5) = 43 - 64 * x at hX
  change g (n + 6) = 85 at hfresh
  have old_bound (r : ℕ) : 0 ≤ ((s.take r).map f).sum ∧
      ((s.take r).map f).sum ≤ 32 * x - 1 := by
    have h := hold.2.2 r
    change 0 ≤ ((sigma.take r).map (fun i => f i.val)).sum ∧
      ((sigma.take r).map (fun i => f i.val)).sum ≤ modulus (n + 6) / 2 at h
    rw [hN] at h
    simpa only [s, ← List.map_take, List.map_map, Function.comp_def] using h
  have new_height (r : ℕ) :
      (((earWord (n + 6) sigma cut).take r).map (actualSource (n + 7) 170)).sum =
      ((s.take (if r ≤ cut then r else r - 1)).map g).sum +
        (if r ≤ cut then 0 else 85) := by
    have he := ear_prefix (n + 6) sigma cut (by omega) (actualSource (n + 7) 170) r
    have hfr : actualSource (n + 7) 170 (Fin.last (n + 6)) = 85 := hfresh
    rw [hfr] at he
    simpa only [s, ← List.map_take, List.map_map, Function.comp_def, actualSource,
      Fin.val_castSucc, Fin.val_last, g, hfresh, Nat.cast_ofNat] using he
  have new_bound (r : ℕ) :
      0 ≤ ((s.take (if r ≤ cut then r else r - 1)).map g).sum +
        (if r ≤ cut then 0 else 85) ∧
      ((s.take (if r ≤ cut then r else r - 1)).map g).sum +
        (if r ≤ cut then 0 else 85) ≤ 64 * x - 1 := by
    have hh := hnew.2.2 r
    rw [new_height, hM] at hh
    exact hh
  let p := s.idxOf (n + 5)
  have hp : p < s.length := List.idxOf_lt_length_of_mem (memall (n + 5) (by omega))
  have step (v : ℕ → ℤ) : ((s.take (p + 1)).map v).sum =
      ((s.take p).map v).sum + v (n + 5) := by
    rw [List.take_add_one, List.getElem?_idxOf (memall (n + 5) (by omega))]
    simp
  let H := ((s.take (p + 1)).map f).sum
  let e : Bool := decide (cut ≤ p)
  let K := ((s.take (p + 1)).map g).sum + 85 * (if e then 1 else 0)
  have hH : 0 ≤ H ∧ H ≤ 42 := by
    have hb := old_bound p
    have ha := old_bound (p + 1)
    rw [step f, hX.1] at ha
    dsimp [H]
    rw [step f, hX.1]
    omega
  have hK : 0 ≤ K ∧ K ≤ 42 := by
    by_cases hc : cut ≤ p
    · have hb := new_bound (p + 1)
      have ha := new_bound (p + 2)
      simp only [ite_eq_right (by omega : ¬ p + 1 ≤ cut),
        ite_eq_right (by omega : ¬ p + 2 ≤ cut), Nat.add_sub_cancel] at hb ha
      have he : p + 2 - 1 = p + 1 := by omega
      simp only [he, step g, hX.2] at ha
      simp only [K, e, hc, decide_true, ite_true, mul_one]
      rw [step g, hX.2]
      omega
    · have hb := new_bound p
      have ha := new_bound (p + 1)
      simp only [ite_eq_left (by omega : p ≤ cut), ite_eq_left (by omega : p + 1 ≤ cut), add_zero] at hb ha
      simp only [K, e, hc, decide_false, Bool.false_eq_true, ite_false, mul_zero, add_zero]
      rw [step g, hX.2] at ha ⊢
      omega
  let S := (s.take (p + 1)).toFinset
  have hS (i : ℕ) (hi : i ∈ S) : i < n + 6 :=
    membound i (List.mem_of_mem_take (List.mem_toFinset.mp hi))
  have smem (i : ℕ) (hi : i < n + 6) : i ∈ S ↔ s.idxOf i ≤ p := by
    simp only [S, List.mem_toFinset, List.mem_take_iff_idxOf_lt (memall i hi)]
    omega
  have hm := u_mass n hn S
  have hr := subset_readout n hn S hS
  have hsum (v : ℕ → ℤ) : (∑ i ∈ S, v i) = ((s.take (p + 1)).map v).sum :=
    List.sum_toFinset v hnd.take
  change (2 * (∑ i ∈ S, f i) = _) ∧ (2 * (∑ i ∈ S, f i) - (∑ i ∈ S, g i) = _) at hr
  simp only [hsum f, hsum g] at hr
  change (2 * H = _) ∧ (2 * H - ((s.take (p + 1)).map g).sum = _) at hr
  have finish (order : Bool) (hu : n - 1 ∉ S)
      (hv : (n + 1 ∈ S ↔ order = true)) (hw : n + 3 ∈ S) : False := by
    let v : Bool := decide (n ∈ S)
    let w : Bool := decide (n + 2 ∈ S)
    let z : Bool := decide (n + 4 ∈ S)
    have hz : n + 5 ∈ S := (smem _ (by omega)).mpr (by exact le_rfl)
    have hb : (if n + 1 ∈ S then (1 : ℤ) else 0) = if order then 1 else 0 := by simp [hv]
    have hrv := hr
    simp only [ite_eq_right hu, ite_eq_left hw, ite_eq_left hz, hb, mul_zero, mul_one, add_zero] at hrv
    apply residue_windows x (∑ i ∈ S, uWeight n i) H K v w z e hx
      (dyadic_residue n h8) hm.2 hH hK order
    · dsimp [v, w, z, x]
      simp only [decide_eq_true_eq]
      cases order <;> by_cases hV : n ∈ S <;> by_cases hW : n + 2 ∈ S <;>
        by_cases hZ : n + 4 ∈ S <;> simp [hV, hW, hZ] at hrv ⊢ <;>
        nlinarith only [hrv.1]
    · dsimp [K, v, w, z]
      simp only [decide_eq_true_eq]
      cases order <;> by_cases hV : n ∈ S <;> by_cases hW : n + 2 ∈ S <;>
        by_cases hZ : n + 4 ∈ S <;> simp [hV, hW, hZ] at hrv ⊢ <;>
        linarith only [hrv.2]
  rcases hord with hord | hord
  · have ho := sublist_positions s hnd _ hord
    have hVX : s.idxOf (n + 1) < s.idxOf (n + 5) :=
      ho.rel_getElem_of_lt (i := 0) (j := 2) (by simp) (by simp) (by decide)
    have hWX : s.idxOf (n + 3) < s.idxOf (n + 5) :=
      ho.rel_getElem_of_lt (i := 1) (j := 2) (by simp) (by simp) (by decide)
    have hXU : s.idxOf (n + 5) < s.idxOf (n - 1) :=
      ho.rel_getElem_of_lt (i := 2) (j := 3) (by simp) (by simp) (by decide)
    have hu : n - 1 ∉ S := by
      rw [smem (n - 1) (by omega)]
      dsimp [p]
      omega
    have hv : n + 1 ∈ S := (smem (n + 1) (by omega)).mpr (by dsimp [p]; omega)
    have hw : n + 3 ∈ S := (smem (n + 3) (by omega)).mpr (by dsimp [p]; omega)
    exact finish true hu ⟨fun _ => rfl, fun _ => hv⟩ hw
  · have ho := sublist_positions s hnd _ hord
    have hWX : s.idxOf (n + 3) < s.idxOf (n + 5) :=
      ho.rel_getElem_of_lt (i := 0) (j := 1) (by simp) (by simp) (by decide)
    have hXU : s.idxOf (n + 5) < s.idxOf (n - 1) :=
      ho.rel_getElem_of_lt (i := 1) (j := 2) (by simp) (by simp) (by decide)
    have hXV : s.idxOf (n + 5) < s.idxOf (n + 1) :=
      ho.rel_getElem_of_lt (i := 1) (j := 3) (by simp) (by simp) (by decide)
    have hu : n - 1 ∉ S := by
      rw [smem (n - 1) (by omega)]
      dsimp [p]
      omega
    have hv : n + 1 ∉ S := by
      rw [smem (n + 1) (by omega)]
      dsimp [p]
      omega
    have hw : n + 3 ∈ S := (smem (n + 3) (by omega)).mpr (by dsimp [p]; omega)
    exact finish false hu ⟨fun h => (hv h).elim, fun h => by cases h⟩ hw

#print axioms actual_source_cyclic_order_residue_obstruction

end D5.S3.Combinatorics.Circle.FourNegative.CyclicOrderResidueObstruction
