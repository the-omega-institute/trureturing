/- GID: D5/S1/Dynamics/Symbolic/GardenOfEden
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/GardenOfEden
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Surjectivity is equivalent to finite-difference preinjectivity for finite alphabets. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BipermutativePreinjectivity
import D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy

/-! The Moore–Myhill theorem for arbitrary two-sided local rules. -/

set_option autoImplicit false

noncomputable section

namespace D5.S1.Dynamics.Symbolic.GardenOfEden

open Set Function
open PermutativeLifts.BipermutativeLift
open PermutativeLifts.BipermutativePreinjectivity

variable {A : Type*} {k : ℕ} {h : (Fin (k + 2) → A) → A}

private theorem code_piecewise_of_collar
    {x y z : ℤ → A} {a b : ℤ}
    (hout : ∀ i, i ∉ Icc a b → x i = y i)
    (hcode : code h x = code h y)
    (hcontext : ∀ i ∈ Icc (a - (k + 1 : ℕ)) (b + (k + 1 : ℕ)), z i = x i) :
    code h ((Icc a b).piecewise y z) = code h z := by
  classical
  funext i
  by_cases htouch : ∃ j : Fin (k + 2), i + (j : ℕ) ∈ Icc a b
  · obtain ⟨j, hj⟩ := htouch
    have hjbound := j.isLt
    have hcollar (t : Fin (k + 2)) :
        i + (t : ℕ) ∈ Icc (a - (k + 1 : ℕ)) (b + (k + 1 : ℕ)) := by
      have ht := t.isLt
      simp only [mem_Icc] at hj ⊢
      omega
    have hz : window (k := k) z i = window x i := by
      funext t
      exact hcontext _ (hcollar t)
    have hw : window (k := k) ((Icc a b).piecewise y z) i = window y i := by
      funext t
      change (Icc a b).piecewise y z (i + (t : ℕ)) = y (i + (t : ℕ))
      by_cases ht : i + (t : ℕ) ∈ Icc a b
      · exact piecewise_eq_of_mem _ _ _ ht
      · rw [piecewise_eq_of_notMem _ _ _ ht]
        exact (hcontext _ (hcollar t)).trans (hout _ ht)
    change h (window ((Icc a b).piecewise y z) i) = h (window z i)
    rw [hw, hz]
    exact (congrFun hcode i).symm
  · apply congrArg h
    funext t
    change (Icc a b).piecewise y z (i + (t : ℕ)) = z (i + (t : ℕ))
    exact piecewise_eq_of_notMem _ _ _ (fun ht => htouch ⟨t, ht⟩)

/-- A failure of native preinjectivity supplies a finite interval containing
two distinct patterns which can be interchanged in every ambient context
realizing the first pattern. The replacement changes finitely many sites,
is nontrivial, and preserves the entire two-sided code image. No finiteness
or nonemptiness hypothesis on the alphabet is needed. -/
private theorem exists_context_independent_collision (hnot : ¬ Preinjective h) :
    ∃ l u : ℤ, l ≤ u ∧ ∃ x y : ℤ → A,
      (∃ i ∈ Icc l u, x i ≠ y i) ∧
      ∀ z : ℤ → A, (∀ i ∈ Icc l u, z i = x i) →
        FiniteDifference ((Icc l u).piecewise y z) z ∧
        (Icc l u).piecewise y z ≠ z ∧
        code h ((Icc l u).piecewise y z) = code h z := by
  classical
  obtain ⟨x, y, hfin, hcode, hne⟩ :
      ∃ x y : ℤ → A, FiniteDifference x y ∧ code h x = code h y ∧ x ≠ y := by
    simpa only [Preinjective, not_forall, not_imp, exists_prop] using hnot
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hne
  obtain ⟨a, ha⟩ := hfin.bddBelow
  obtain ⟨b, hb⟩ := hfin.bddAbove
  have hab : a ≤ b := (ha hi).trans (hb hi)
  have hout : ∀ j, j ∉ Icc a b → x j = y j := by
    intro j hj
    by_contra hxy
    exact hj ⟨ha hxy, hb hxy⟩
  let l := a - (k + 1 : ℕ)
  let u := b + (k + 1 : ℕ)
  have hsub : Icc a b ⊆ Icc l u := by
    intro j hj
    dsimp [l, u]
    simp only [mem_Icc] at hj ⊢
    omega
  refine ⟨l, u, by dsimp [l, u]; omega, x, y, ⟨i, hsub ⟨ha hi, hb hi⟩, hi⟩, ?_⟩
  intro z hz
  refine ⟨?_, ?_, ?_⟩
  · apply (finite_Icc l u).subset
    intro j hj
    by_contra hjout
    exact hj (piecewise_eq_of_notMem _ _ _ hjout)
  · intro he
    have heq := congrFun he i
    rw [piecewise_eq_of_mem _ _ _ (hsub ⟨ha hi, hb hi⟩), hz i (hsub ⟨ha hi, hb hi⟩)] at heq
    exact hi heq.symm
  · have hpatch : (Icc l u).piecewise y z = (Icc a b).piecewise y z := by
      funext j
      by_cases hj : j ∈ Icc a b
      · rw [piecewise_eq_of_mem _ _ _ hj, piecewise_eq_of_mem _ _ _ (hsub hj)]
      · rw [piecewise_eq_of_notMem _ _ _ hj]
        by_cases hjlu : j ∈ Icc l u
        · rw [piecewise_eq_of_mem _ _ _ hjlu]
          exact (hout j hj).symm.trans (hz j hjlu).symm
        · exact piecewise_eq_of_notMem _ _ _ hjlu
    rw [hpatch]
    exact code_piecewise_of_collar hout hcode hz

/-- Insert a finite word at an arbitrary integer site, retaining the ambient
configuration outside the half-open insertion interval. -/
def writeWord {n : ℕ} (p : Fin n → A) (t : ℤ) (z : ℤ → A) : ℤ → A :=
  fun i => if hi : t ≤ i ∧ i < t + n then p ⟨(i - t).toNat, by omega⟩ else z i

theorem writeWord_at {n : ℕ} (p : Fin n → A) (t : ℤ) (z : ℤ → A)
    (j : Fin n) : writeWord p t z (t + (j : ℕ)) = p j := by
  have hj := j.isLt
  simp only [writeWord]
  split_ifs with hi
  · congr 1
    apply Fin.ext
    change (t + (j : ℕ) - t).toNat = j.val
    omega
  · omega

/-- Nonpreinjectivity yields distinct words of positive common length such
that every occurrence of the first can be replaced by the second without
changing any coordinate of the full two-sided code image. -/
theorem exists_erasable_words (hnot : ¬ Preinjective h) :
    ∃ n : ℕ, 0 < n ∧ ∃ p q : Fin n → A, p ≠ q ∧
      ∀ (t : ℤ) (z : ℤ → A), (∀ j : Fin n, z (t + (j : ℕ)) = p j) →
        code h (writeWord q t z) = code h z := by
  classical
  obtain ⟨l, u, hlu, x, y, ⟨i, hi, hxy⟩, hreplace⟩ :=
    exists_context_independent_collision hnot
  let n := (u - l + 1).toNat
  have hn : 0 < n := by dsimp [n]; omega
  have hlen : (n : ℤ) = u - l + 1 := by dsimp [n]; omega
  let p : Fin n → A := fun j => x (l + (j : ℕ))
  let q : Fin n → A := fun j => y (l + (j : ℕ))
  have hpq : p ≠ q := by
    intro he
    let j : Fin n := ⟨(i - l).toNat, by simp only [mem_Icc] at hi; omega⟩
    have hj : l + (j : ℕ) = i := by dsimp [j]; simp only [mem_Icc] at hi; omega
    have heq := congrFun he j
    exact hxy (by simpa only [p, q, hj] using heq)
  refine ⟨n, hn, p, q, hpq, ?_⟩
  intro t z hz
  let z' : ℤ → A := fun j => z (t + (j - l))
  have hz' : ∀ j ∈ Icc l u, z' j = x j := by
    intro j hj
    let a : Fin n := ⟨(j - l).toNat, by simp only [mem_Icc] at hj; omega⟩
    have ha : l + (a : ℕ) = j := by dsimp [a]; simp only [mem_Icc] at hj; omega
    have hja : (a : ℤ) = j - l := by omega
    calc
      z' j = z (t + (a : ℕ)) := by dsimp [z']; rw [hja]
      _ = x (l + (a : ℕ)) := hz a
      _ = x j := by rw [ha]
  have he := (hreplace z' hz').2.2
  have hpaste : (Icc l u).piecewise y z' =
      SymbolicDynamics.FullShift.shift (t - l) (writeWord q t z) := by
    funext j
    simp only [SymbolicDynamics.FullShift.shift_apply, writeWord]
    by_cases hj : j ∈ Icc l u
    · rw [piecewise_eq_of_mem _ _ _ hj]
      have hji : t ≤ t - l + j ∧ t - l + j < t + n := by
        simp only [mem_Icc] at hj
        omega
      rw [dite_eq_left hji]
      dsimp only [q]
      congr 1
      omega
    · rw [piecewise_eq_of_notMem _ _ _ hj]
      have hji : ¬ (t ≤ t - l + j ∧ t - l + j < t + n) := by
        simp only [mem_Icc] at hj
        omega
      rw [dite_eq_right hji]
      dsimp [z']
      congr 1
      omega
  have hzshift : z' = SymbolicDynamics.FullShift.shift (t - l) z := by
    funext j
    simp only [z', SymbolicDynamics.FullShift.shift_apply]
    congr 1
    omega
  rw [hpaste, hzshift, code_shift, code_shift] at he
  funext j
  have heq := congrFun he (j - (t - l))
  simpa only [SymbolicDynamics.FullShift.shift_apply, add_sub_cancel] using heq

/-- One-sided rays actually obtained by restricting complete two-sided code
images. This is a spatial language, with no iteration of the local rule. -/
def imageRay (h : (Fin (k + 2) → A) → A) : Set (ℕ → A) :=
  {z | ∃ x : ℤ → A, ∀ n : ℕ, z n = code h x (n : ℤ)}

private def eraseBlocks {m : ℕ} (p q : Fin m → A) (n : ℕ) (x : ℤ → A) : ℤ → A :=
  match n with
  | 0 => x
  | n + 1 => by
    classical
    let z := eraseBlocks p q n x
    exact if (fun j : Fin m => z ((n * m : ℕ) + (j : ℕ))) = p then
      writeWord q (n * m : ℕ) z else z

private theorem eraseBlocks_code {m : ℕ} (p q : Fin m → A)
    (herase : ∀ (t : ℤ) (z : ℤ → A), (∀ j : Fin m, z (t + (j : ℕ)) = p j) →
      code h (writeWord q t z) = code h z) (n : ℕ) (x : ℤ → A) :
    code h (eraseBlocks p q n x) = code h x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    classical
    simp only [eraseBlocks]
    split_ifs with hc
    · exact (herase _ _ (fun j => congrFun hc j)).trans ih
    · exact ih

private theorem eraseBlocks_avoids {m : ℕ} (p q : Fin m → A)
    (hpq : p ≠ q) (n : ℕ) (x : ℤ → A) (j : Fin n) :
    (fun r : Fin m => eraseBlocks p q n x ((j.val * m : ℕ) + (r : ℕ))) ≠ p := by
  classical
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    by_cases hj : j.val < n
    · have heq :
          (fun r : Fin m => eraseBlocks p q (n + 1) x ((j.val * m : ℕ) + (r : ℕ))) =
          (fun r : Fin m => eraseBlocks p q n x ((j.val * m : ℕ) + (r : ℕ))) := by
        funext r
        have hbound := Nat.mul_le_mul_right m (show j.val + 1 ≤ n by omega)
        have hr := r.isLt
        have hlt : ((j.val * m : ℕ) : ℤ) + (r : ℕ) < (n * m : ℕ) := by
          exact_mod_cast (show j.val * m + r.val < n * m by nlinarith)
        simp only [eraseBlocks]
        split_ifs
        · simp only [writeWord]
          rw [dite_eq_right (by omega)]
        · rfl
      rw [heq]
      exact ih ⟨j.val, hj⟩
    · have hjn : j.val = n := by omega
      simp only [hjn, eraseBlocks]
      split_ifs with hc
      · simpa only [writeWord_at] using hpq.symm
      · exact hc

private abbrev ImagePrefix (h : (Fin (k + 2) → A) → A) (n : ℕ) :=
  Set.range fun x : ℤ → A => fun i : Fin n => code h x (i : ℕ)

private theorem prefixCount_eq (n : ℕ) :
    PrefixGrowthEntropy.prefixCount (imageRay h) n = Nat.card (ImagePrefix h n) := by
  unfold PrefixGrowthEntropy.prefixCount ImagePrefix
  congr 1
  apply congrArg (fun s : Set (Fin n → A) => ↥s)
  ext w
  constructor
  · rintro ⟨⟨z, x, hx⟩, hw⟩
    refine ⟨x, ?_⟩
    funext i
    exact (hx i.val).symm.trans (congrFun hw i)
  · rintro ⟨x, rfl⟩
    exact ⟨⟨fun n => code h x n, x, fun _ => rfl⟩, rfl⟩

private theorem prefixCount_le_of_erasable [Fintype A]
    {m : ℕ} (hm : 0 < m) (p q : Fin m → A) (hpq : p ≠ q)
    (herase : ∀ (t : ℤ) (z : ℤ → A), (∀ j : Fin m, z (t + (j : ℕ)) = p j) →
      code h (writeWord q t z) = code h z) (n : ℕ) :
    PrefixGrowthEntropy.prefixCount (imageRay h) (n * m) ≤
      (Fintype.card A ^ m - 1) ^ n * Fintype.card A ^ (k + 1) := by
  classical
  let B := {w : Fin m → A // w ≠ p}
  let source (u : ImagePrefix h (n * m)) : ℤ → A := Classical.choose u.property
  have hsource (u : ImagePrefix h (n * m)) (i : Fin (n * m)) :
      code h (source u) (i : ℕ) = u.val i :=
    congrFun (Classical.choose_spec u.property) i
  let norm (u : ImagePrefix h (n * m)) := eraseBlocks p q n (source u)
  have hnorm (u : ImagePrefix h (n * m)) : code h (norm u) = code h (source u) :=
    eraseBlocks_code p q herase n (source u)
  let key : ImagePrefix h (n * m) → (Fin n → B) × (Fin (k + 1) → A) := fun u =>
    (fun j => ⟨fun r => norm u ((j.val * m : ℕ) + (r : ℕ)),
      eraseBlocks_avoids p q hpq n (source u) j⟩,
     fun r => norm u ((n * m : ℕ) + (r : ℕ)))
  have hkey : Injective key := by
    intro u v he
    have hblocks := congrArg Prod.fst he
    have htail := congrArg Prod.snd he
    have hsame (a : ℕ) (ha : a < n * m + (k + 1)) : norm u a = norm v a := by
      by_cases hb : a < n * m
      · have hj : a / m < n := (Nat.div_lt_iff_lt_mul hm).mpr hb
        let j : Fin n := ⟨a / m, hj⟩
        let r : Fin m := ⟨a % m, Nat.mod_lt _ hm⟩
        have hr := congrFun (congrArg Subtype.val (congrFun hblocks j)) r
        have haeq : a / m * m + a % m = a := Nat.div_add_mod' a m
        change norm u ((a / m * m : ℕ) + (a % m : ℕ)) =
          norm v ((a / m * m : ℕ) + (a % m : ℕ)) at hr
        simpa only [← Nat.cast_add, haeq] using hr
      · let r : Fin (k + 1) := ⟨a - n * m, by omega⟩
        have hr := congrFun htail r
        have haeq : n * m + (a - n * m) = a := by omega
        change norm u ((n * m : ℕ) + (a - n * m : ℕ)) =
          norm v ((n * m : ℕ) + (a - n * m : ℕ)) at hr
        simpa only [← Nat.cast_add, haeq] using hr
    apply Subtype.ext
    funext i
    calc
      u.val i = code h (norm u) (i : ℕ) :=
        ((congrFun (hnorm u) (i : ℕ)).trans (hsource u i)).symm
      _ = code h (norm v) (i : ℕ) := by
        apply congrArg h
        funext j
        change norm u ((i : ℕ) + (j : ℕ)) = norm v ((i : ℕ) + (j : ℕ))
        simp only [← Nat.cast_add]
        exact hsame (i.val + j.val) (by have hi := i.isLt; have hj := j.isLt; omega)
      _ = v.val i := (congrFun (hnorm v) (i : ℕ)).trans (hsource v i)
  have hb : Fintype.card B = Fintype.card A ^ m - 1 := by
    dsimp only [B]
    rw [Fintype.card_subtype_compl (fun w : Fin m → A => w = p)]
    simp
  rw [prefixCount_eq]
  have hc := Nat.card_le_card_of_injective key hkey
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, hb] using hc

private theorem image_count_pos [Finite A] [Nonempty A] (N : ℕ) :
    (0 : ℝ) < PrefixGrowthEntropy.prefixCount (imageRay h) N := by
  have : Nonempty (ImagePrefix h N) :=
    ⟨⟨fun i => code h (fun _ => Classical.choice ‹Nonempty A›) (i : ℕ),
      fun _ => Classical.choice ‹Nonempty A›, rfl⟩⟩
  rw [prefixCount_eq]
  exact_mod_cast (Nat.card_pos (α := ImagePrefix h N))

private theorem image_prefix_growth [Finite A] [Nonempty A] :
    ∃ r : ℝ, Filter.Tendsto
      (fun n : ℕ => Real.log (PrefixGrowthEntropy.prefixCount (imageRay h) n : ℝ) / n)
      Filter.atTop (nhds r) := by
  let : Fintype A := Fintype.ofFinite A
  let : UniformSpace A := ⊥
  have hne : (imageRay h).Nonempty :=
    ⟨fun n => code h (fun _ => Classical.choice ‹Nonempty A›) n,
      fun _ => Classical.choice ‹Nonempty A›, fun _ => rfl⟩
  have hinv : MapsTo (SymbolicDynamics.FullShift.shift (1 : ℕ)) (imageRay h) (imageRay h) := by
    rintro z ⟨x, hx⟩
    refine ⟨SymbolicDynamics.FullShift.shift (1 : ℤ) x, ?_⟩
    intro n
    rw [code_shift]
    simpa only [SymbolicDynamics.FullShift.shift_apply, Nat.cast_add, Nat.cast_one] using hx (1 + n)
  obtain ⟨r, _, _, hlim, _⟩ :=
    PrefixGrowthEntropy.prefix_growth_entropy (imageRay h) hne hinv
  exact ⟨r, hlim⟩

private theorem rate_le_of_block_bound {f : ℕ → ℕ} {r : ℝ} {m B C : ℕ}
    (hf : ∀ n, (0 : ℝ) < f n)
    (hlim : Filter.Tendsto (fun n : ℕ => Real.log (f n : ℝ) / n) Filter.atTop (nhds r))
    (hm : 0 < m) (hB : 0 < B) (hC : 0 < C)
    (hbound : ∀ n, f (n * m) ≤ B ^ n * C) : r ≤ Real.log B / m := by
  have hmul : Filter.Tendsto (fun n : ℕ => n * m) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => show n ≤ n * m by nlinarith) Filter.tendsto_id
  have hrhs : Filter.Tendsto
      (fun n : ℕ => ((n : ℝ) * Real.log B + Real.log C) / ((n : ℝ) * m))
      Filter.atTop (nhds (Real.log B / m)) := by
    simpa only [zero_add, add_zero, mul_comm, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (Real.log C) 0 (Real.log B)
        (d := (m : ℝ)) (by exact_mod_cast hm.ne'))
  apply le_of_tendsto_of_tendsto (hlim.comp hmul) hrhs
  apply Filter.Eventually.of_forall
  intro n
  dsimp only [Function.comp_def]
  have hlog : Real.log (f (n * m) : ℝ) ≤ (n : ℝ) * Real.log B + Real.log C := by
    calc
      _ ≤ Real.log ((B : ℝ) ^ n * C) := Real.log_le_log (hf _)
        (by exact_mod_cast hbound n)
      _ = _ := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  simpa only [Nat.cast_mul] using div_le_div_of_nonneg_right hlog
    (show (0 : ℝ) ≤ (n : ℝ) * m by positivity)

/-- A native finite collision forces a strict loss in the logarithmic growth
of actual image prefixes. The limiting rate concerns spatial prefixes of
complete images, rather than temporal entropy of the local-code map. -/
theorem strict_image_prefix_loss [Finite A] (hq : 2 ≤ Nat.card A)
    (hnot : ¬ Preinjective h) :
    ∃ r : ℝ, r < Real.log (Nat.card A : ℝ) ∧
      Filter.Tendsto
        (fun n : ℕ => Real.log (PrefixGrowthEntropy.prefixCount (imageRay h) n : ℝ) / n)
        Filter.atTop (nhds r) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hq' : 2 ≤ Fintype.card A := by simpa only [Nat.card_eq_fintype_card] using hq
  have : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨m, hm, p, q, hpq, herase⟩ := exists_erasable_words hnot
  obtain ⟨r, hlim⟩ := image_prefix_growth (h := h)
  let B := Fintype.card A ^ m - 1
  have hpow : 1 < Fintype.card A ^ m := one_lt_pow' (by omega) hm.ne'
  have hBpos : (0 : ℝ) < B := by
    dsimp [B]
    exact_mod_cast (show 0 < Fintype.card A ^ m - 1 by omega)
  have hle : r ≤ Real.log B / m :=
    rate_le_of_block_bound (image_count_pos (h := h)) hlim hm
      (by exact_mod_cast hBpos)
      (pow_pos (by omega) _) (prefixCount_le_of_erasable hm p q hpq herase)
  have hstrict : Real.log B / (m : ℝ) < Real.log (Fintype.card A) := by
    have hlt : (B : ℝ) < (Fintype.card A : ℝ) ^ m := by
      exact_mod_cast (show B < Fintype.card A ^ m by dsimp [B]; omega)
    have hlog := Real.log_lt_log hBpos hlt
    rw [Real.log_pow] at hlog
    exact (div_lt_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mpr
      (by simpa only [mul_comm] using hlog)
  exact ⟨r, by simpa only [Nat.card_eq_fintype_card] using hle.trans_lt hstrict, hlim⟩

private theorem missing_word_of_not_surjective [Finite A]
    (hns : ¬ Surjective (code h)) :
    ∃ m : ℕ, 0 < m ∧ ∃ p : Fin m → A,
      ∀ (x : ℤ → A) (t : ℤ), (fun j : Fin m => code h x (t + (j : ℕ))) ≠ p := by
  classical
  let : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have hclosed : IsClosed (range (code h)) := (isCompact_range (continuous_code h)).isClosed
  obtain ⟨y, hy⟩ : ∃ y : ℤ → A, y ∉ range (code h) := by
    simpa only [Surjective, mem_range, not_forall] using hns
  obtain ⟨s, U, hU, hsub⟩ := isOpen_pi_iff.mp hclosed.isOpen_compl y hy
  obtain ⟨a, ha⟩ := s.finite_toSet.bddBelow
  obtain ⟨b, hb⟩ := s.finite_toSet.bddAbove
  let m := (max a b - a + 1).toNat
  have hm : 0 < m := by dsimp [m]; omega
  have hlen : (m : ℤ) = max a b - a + 1 := by dsimp [m]; omega
  let p : Fin m → A := fun j => y (a + (j : ℕ))
  refine ⟨m, hm, p, ?_⟩
  intro x t he
  let x' := SymbolicDynamics.FullShift.shift (t - a) x
  have hmatch : code h x' ∈ (s : Set ℤ).pi U := by
    intro i hi
    have hai : a ≤ i := ha hi
    have hbi : i ≤ b := hb hi
    let j : Fin m := ⟨(i - a).toNat, by omega⟩
    have hj : a + (j : ℕ) = i := by dsimp [j]; omega
    have heq := congrFun he j
    change code h x (t + (j : ℕ)) = y (a + (j : ℕ)) at heq
    have hout : code h x' i = y i := by
      dsimp [x']
      rw [code_shift]
      change code h x (t - a + i) = y i
      rw [← hj]
      convert heq using 1
      congr 1
      omega
    rw [hout]
    exact (hU i hi).2
  exact (hsub hmatch) ⟨x', rfl⟩

private theorem prefixCount_le_of_missing_word [Fintype A]
    {m : ℕ} (hm : 0 < m) (p : Fin m → A)
    (hmissing : ∀ (x : ℤ → A) (t : ℤ),
      (fun j : Fin m => code h x (t + (j : ℕ))) ≠ p) (n : ℕ) :
    PrefixGrowthEntropy.prefixCount (imageRay h) (n * m) ≤
      (Fintype.card A ^ m - 1) ^ n := by
  classical
  let B := {w : Fin m → A // w ≠ p}
  let source (u : ImagePrefix h (n * m)) : ℤ → A := Classical.choose u.property
  have hsource (u : ImagePrefix h (n * m)) (i : Fin (n * m)) :
      code h (source u) (i : ℕ) = u.val i :=
    congrFun (Classical.choose_spec u.property) i
  let key : ImagePrefix h (n * m) → (Fin n → B) := fun u j =>
    ⟨fun r => code h (source u) ((j.val * m : ℕ) + (r : ℕ)), hmissing _ _⟩
  have hkey : Injective key := by
    intro u v he
    apply Subtype.ext
    funext i
    have hj : i.val / m < n := (Nat.div_lt_iff_lt_mul hm).mpr i.isLt
    let j : Fin n := ⟨i.val / m, hj⟩
    let r : Fin m := ⟨i.val % m, Nat.mod_lt _ hm⟩
    have hr := congrFun (congrArg Subtype.val (congrFun he j)) r
    have hi : i.val / m * m + i.val % m = i.val := Nat.div_add_mod' i.val m
    change code h (source u) ((i.val / m * m : ℕ) + (i.val % m : ℕ)) =
      code h (source v) ((i.val / m * m : ℕ) + (i.val % m : ℕ)) at hr
    simp only [← Nat.cast_add, hi] at hr
    exact (hsource u i).symm.trans (hr.trans (hsource v i))
  have hb : Fintype.card B = Fintype.card A ^ m - 1 := by
    dsimp only [B]
    rw [Fintype.card_subtype_compl (fun w : Fin m → A => w = p)]
    simp
  rw [prefixCount_eq]
  have hc := Nat.card_le_card_of_injective key hkey
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hb] using hc

private theorem prefixCount_lower_of_preinjective [Fintype A] [Nonempty A]
    (hpre : Preinjective h) (n : ℕ) :
    Fintype.card A ^ n ≤ PrefixGrowthEntropy.prefixCount (imageRay h) (n + (k + 1)) := by
  classical
  let c : ℤ → A := fun _ => Classical.choice ‹Nonempty A›
  let lift (w : Fin n → A) := writeWord w (k + 1 : ℕ) c
  let key : (Fin n → A) → ImagePrefix h (n + (k + 1)) := fun w =>
    ⟨fun i => code h (lift w) (i : ℕ), lift w, rfl⟩
  have hkey : Injective key := by
    intro w v he
    have hfin : FiniteDifference (lift w) (lift v) := by
      apply (finite_Ico (k + 1 : ℤ) ((k + 1 : ℤ) + n)).subset
      intro i hi
      by_contra hout
      apply hi
      dsimp [lift, writeWord]
      rw [dite_eq_right (by simpa only [mem_Ico, Nat.cast_add, Nat.cast_one] using hout),
        dite_eq_right (by simpa only [mem_Ico, Nat.cast_add, Nat.cast_one] using hout)]
    have hcode : code h (lift w) = code h (lift v) := by
      funext i
      by_cases hi : 0 ≤ i ∧ i < n + (k + 1 : ℕ)
      · let j : Fin (n + (k + 1)) := ⟨i.toNat, by omega⟩
        have hj := congrFun (congrArg Subtype.val he) j
        simpa only [key, j, Int.natCast_toNat_eq_self.mpr hi.1] using hj
      · apply congrArg h
        funext j
        have hj := j.isLt
        change writeWord w (k + 1 : ℕ) c (i + (j : ℕ)) =
          writeWord v (k + 1 : ℕ) c (i + (j : ℕ))
        dsimp only [writeWord]
        rw [dite_eq_right (by omega), dite_eq_right (by omega)]
    have hinput := hpre hfin hcode
    funext j
    have hj := congrFun hinput ((k + 1 : ℕ) + (j : ℕ))
    simpa only [lift, writeWord_at] using hj
  rw [prefixCount_eq]
  have hc := Nat.card_le_card_of_injective key hkey
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using hc

private theorem prefixCount_full [Fintype A] [Nonempty A]
    (hsurj : Surjective (code h)) (n : ℕ) :
    PrefixGrowthEntropy.prefixCount (imageRay h) n = Fintype.card A ^ n := by
  classical
  have hfull : ImagePrefix h n = univ := by
    apply eq_univ_of_forall
    intro w
    let c : ℤ → A := fun _ => Classical.choice ‹Nonempty A›
    obtain ⟨x, hx⟩ := hsurj (writeWord w 0 c)
    refine ⟨x, ?_⟩
    funext i
    have hi := writeWord_at w 0 c i
    simpa only [hx, zero_add] using hi
  rw [prefixCount_eq, hfull, Nat.card_univ]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

private theorem rate_ge_of_preinjective [Fintype A] [Nonempty A]
    (hpre : Preinjective h) {r : ℝ}
    (hlim : Filter.Tendsto
      (fun n : ℕ => Real.log (PrefixGrowthEntropy.prefixCount (imageRay h) n : ℝ) / n)
      Filter.atTop (nhds r)) : Real.log (Fintype.card A) ≤ r := by
  have hqpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hlower : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * Real.log (Fintype.card A) / (n + (k + 1 : ℕ)))
      Filter.atTop (nhds (Real.log (Fintype.card A))) := by
    simpa only [zero_add, mul_one, one_mul, div_one, mul_comm, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds 0 ((k + 1 : ℕ) : ℝ)
        (Real.log (Fintype.card A)) (d := (1 : ℝ)) one_ne_zero)
  apply le_of_tendsto_of_tendsto hlower (hlim.comp (Filter.tendsto_add_atTop_nat (k + 1)))
  apply Filter.Eventually.of_forall
  intro n
  have hc := prefixCount_lower_of_preinjective hpre n
  have hlog : (n : ℝ) * Real.log (Fintype.card A) ≤
      Real.log (PrefixGrowthEntropy.prefixCount (imageRay h) (n + (k + 1)) : ℝ) := by
    calc
      _ = Real.log ((Fintype.card A : ℝ) ^ n) := (Real.log_pow _ _).symm
      _ ≤ _ := Real.log_le_log (pow_pos hqpos _) (by exact_mod_cast hc)
  simpa only [Function.comp_def, Nat.cast_add] using
    div_le_div_of_nonneg_right hlog (show (0 : ℝ) ≤ n + (k + 1 : ℕ) by positivity)

/-- The Moore–Myhill Garden-of-Eden theorem for arbitrary finite-alphabet
two-sided local rules, using the original native surjectivity and
finite-difference preinjectivity predicates. Empty and singleton alphabets
are included. -/
theorem garden_of_eden [Finite A] (k : ℕ) (h : (Fin (k + 2) → A) → A) :
    Surjective (code h) ↔ Preinjective h := by
  classical
  by_cases hA : Subsingleton A
  · have : Subsingleton A := hA
    constructor
    · intro _ x y _ _
      exact Subsingleton.elim x y
    · intro _ y
      exact ⟨y, Subsingleton.elim _ _⟩
  have : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
  let : Fintype A := Fintype.ofFinite A
  have hq : 2 ≤ Fintype.card A := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hqNat : 2 ≤ Nat.card A := by simpa only [Nat.card_eq_fintype_card] using hq
  constructor
  · intro hsurj
    by_contra hnot
    obtain ⟨r, hr, hlim⟩ := strict_image_prefix_loss hqNat hnot
    have hfull : Filter.Tendsto
        (fun n : ℕ => Real.log (PrefixGrowthEntropy.prefixCount (imageRay h) n : ℝ) / n)
        Filter.atTop (nhds (Real.log (Fintype.card A))) := by
      refine (tendsto_const_nhds : Filter.Tendsto
        (fun _ : ℕ => Real.log (Fintype.card A)) Filter.atTop _).congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [prefixCount_full hsurj, Nat.cast_pow, Real.log_pow]
      exact (mul_div_cancel_left₀ (Real.log (Fintype.card A))
        (by exact_mod_cast (show n ≠ 0 by omega))).symm
    have he := tendsto_nhds_unique hlim hfull
    exact (ne_of_lt (by simpa only [Nat.card_eq_fintype_card] using hr)) he
  · intro hpre
    by_contra hns
    obtain ⟨m, hm, p, hmissing⟩ := missing_word_of_not_surjective hns
    obtain ⟨r, hlim⟩ := image_prefix_growth (h := h)
    have hlower := rate_ge_of_preinjective hpre hlim
    let B := Fintype.card A ^ m - 1
    have hpow : 1 < Fintype.card A ^ m := one_lt_pow' (by omega) hm.ne'
    have hBpos : 0 < B := by dsimp [B]; omega
    have hupper : r ≤ Real.log B / m :=
      rate_le_of_block_bound (image_count_pos (h := h)) hlim hm hBpos (by norm_num : 0 < 1)
        (fun n => by simpa only [mul_one] using prefixCount_le_of_missing_word hm p hmissing n)
    have hlt : (B : ℝ) < (Fintype.card A : ℝ) ^ m := by
      exact_mod_cast (show B < Fintype.card A ^ m by dsimp [B]; omega)
    have hlog := Real.log_lt_log (by exact_mod_cast hBpos) hlt
    rw [Real.log_pow] at hlog
    have hstrict : Real.log B / (m : ℝ) < Real.log (Fintype.card A) :=
      (div_lt_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mpr
        (by simpa only [mul_comm] using hlog)
    exact (not_lt_of_ge hlower) (hupper.trans_lt hstrict)

end D5.S1.Dynamics.Symbolic.GardenOfEden
