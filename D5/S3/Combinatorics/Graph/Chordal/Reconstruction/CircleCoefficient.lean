/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/CircleCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact ambient unit-quaternion reconstruction coefficient for circle gains on finite path powers. -/

import D5.S3.Combinatorics.Graph.Chordal.QuaternionCircleBlockFit
import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalBanachExactStrata

/-! The ambient unit-quaternion coefficient is one for circle-valued gains on finite path powers. -/

open scoped Quaternion InnerProductSpace
noncomputable section

namespace SimpleGraph.CirclePowerPath

open Real Omega.Geometry.UnitQuaternion

variable {V : Type*} {G : SimpleGraph V}

local notation "powerPath" => BanachPathPower.pathPower

private def powerAnchor {n k : ℕ} (i : Fin n) : Fin n :=
  ⟨i.val / k * k, (Nat.div_mul_le_self _ _).trans_lt i.isLt⟩

private theorem powerPath_anchor {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    powerAnchor (k := k) i = i ∨ (powerPath n k).Adj (powerAnchor (k := k) i) i := by
  by_cases he : powerAnchor (k := k) i = i
  · exact Or.inl he
  · refine Or.inr ⟨he, ?_, ?_⟩
    · exact (Nat.div_mul_le_self _ _).trans (Nat.le_add_right _ _)
    · have hd : i.val % k + i.val / k * k = i.val := by
        simpa [Nat.mul_comm] using Nat.mod_add_div i.val k
      have hm := Nat.mod_lt i.val hk
      change i.val ≤ i.val / k * k + k
      omega

private theorem powerPath_blocks {n k : ℕ} (hk : 0 < k) (i j : Fin n)
    (hij : (powerPath n k).Adj i j) :
    i.val / k = j.val / k ∨ i.val / k + 1 = j.val / k ∨
      j.val / k + 1 = i.val / k := by
  have hi := Nat.div_le_div_right (c := k) hij.2.1
  have hj := Nat.div_le_div_right (c := k) hij.2.2
  rw [Nat.add_div_right _ hk] at hi hj
  omega

/-- The large-defect half of coefficient one for every positive power-path width. -/
private theorem powerPath_large_defect {n k : ℕ} (hk : 0 < k) (b : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, phase (b i i) = 1)
    (hrev : ∀ i j, (powerPath n k).Adj i j → phase (b j i) = (phase (b i j))⁻¹)
    {δ : ℝ} (hδ : π / 2 ≤ δ)
    (htri : TriangleBound (powerPath n k) (fun i j => phase (b i j)) δ) :
    ∃ p : Fin n → U, Fits (powerPath n k) (fun i j => phase (b i j)) p δ := by
  rw [← max_eq_left hδ]
  exact alternating_blocks_fit b hdiag hrev (fun i => i.val / k) powerAnchor
    (powerPath_anchor hk) (fun i j h => Fin.ext (by simp [powerAnchor, h]))
    (powerPath_blocks hk) (by linarith [pi_pos]) htri

private def faceAngle (b : ℕ → ℕ → ℝ) (i j l : ℕ) : ℝ :=
  if i < j ∧ j < l then (exists_principal (b i j + b j l - b i l)).choose else 0

private theorem faceAngle_spec (b : ℕ → ℕ → ℝ) {i j l : ℕ} (hij : i < j) (hjl : j < l) :
    |faceAngle b i j l| ≤ π ∧
      phase (faceAngle b i j l) = phase (b i j + b j l - b i l) ∧
      roundDist (phase (b i j + b j l - b i l)) 1 = |faceAngle b i j l| := by
  simpa [faceAngle, hij, hjl] using
    (exists_principal (b i j + b j l - b i l)).choose_spec

private theorem faceAngle_bound {n k : ℕ} (b : ℕ → ℕ → ℝ) {δ : ℝ}
    (htri : ∀ i j l, i < j → j < l → l < n → l ≤ i + k →
      roundDist (phase (b i j) * phase (b j l)) (phase (b i l)) ≤ δ)
    {i j l : ℕ} (hij : i < j) (hjl : j < l) (hln : l < n) (hspan : l ≤ i + k) :
    |faceAngle b i j l| ≤ δ := by
  have hh := htri i j l hij hjl hln hspan
  rw [← phase_add, ← round_mul_right (phase (b i l))⁻¹, ← phase_sub,
    mul_inv_cancel] at hh
  rwa [(faceAngle_spec b hij hjl).2.2] at hh

private theorem faceAngle_tetra {n k : ℕ} (b : ℕ → ℕ → ℝ) {δ : ℝ}
    (hδ : δ < π / 2)
    (htri : ∀ i j l, i < j → j < l → l < n → l ≤ i + k →
      roundDist (phase (b i j) * phase (b j l)) (phase (b i l)) ≤ δ)
    {i j l m : ℕ} (hij : i < j) (hjl : j < l) (hlm : l < m)
    (hmn : m < n) (hspan : m ≤ i + k) :
    faceAngle b j l m - faceAngle b i l m + faceAngle b i j m -
      faceAngle b i j l = 0 := by
  have h₁ := faceAngle_bound b htri hjl hlm hmn (by omega)
  have h₂ := faceAngle_bound b htri (by omega : i < l) hlm hmn hspan
  have h₃ := faceAngle_bound b htri hij (by omega : j < m) hmn hspan
  have h₄ := faceAngle_bound b htri hij hjl (by omega) (by omega)
  apply phase_injective_near_zero
  · apply abs_lt.mpr
    have ha := abs_le.mp h₁
    have hb := abs_le.mp h₂
    have hc := abs_le.mp h₃
    have hd := abs_le.mp h₄
    constructor <;> linarith
  · simp only [phase_sub, phase_add, (faceAngle_spec b hjl hlm).2.1,
      (faceAngle_spec b (by omega : i < l) hlm).2.1,
      (faceAngle_spec b hij (by omega : j < m)).2.1, (faceAngle_spec b hij hjl).2.1]
    simp only [← phase_neg, ← phase_add]
    convert phase_zero using 1; congr 1; ring

/-- Integrate faces by repeatedly removing the first vertex of an interval. -/
private def forwardLift (b : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | i, d + 1 => b i (i + 1) + forwardLift b (i + 1) d - faceAngle b i (i + 1) (i + d + 1)

private theorem forwardLift_step (b : ℕ → ℕ → ℝ) {i j : ℕ} (hij : i < j) :
    forwardLift b i (j - i) = b i (i + 1) + forwardLift b (i + 1) (j - (i + 1)) -
      faceAngle b i (i + 1) j := by
  have hd : j - i = (j - (i + 1)) + 1 := by omega
  rw [hd, forwardLift]
  congr 2
  omega

private theorem forwardLift_phase (b : ℕ → ℕ → ℝ) {i j : ℕ} (hij : i < j) :
    phase (forwardLift b i (j - i)) = phase (b i j) := by
  generalize hd : j - i = d
  induction d using Nat.strong_induction_on generalizing i j with
  | h d ih =>
    rw [← hd, forwardLift_step b hij]
    by_cases he : j = i + 1
    · subst j
      simp [forwardLift, faceAngle]
    · have hsmall : j - (i + 1) < d := by omega
      have hp := ih _ hsmall (by omega : i + 1 < j) rfl
      rw [phase_sub, phase_add, hp, (faceAngle_spec b (by omega : i < i + 1)
        (by omega : i + 1 < j)).2.1, ← phase_add, ← phase_sub]
      congr 1
      ring

private theorem forwardLift_triangle {n k : ℕ} (b : ℕ → ℕ → ℝ) {δ : ℝ}
    (hδ : δ < π / 2)
    (htri : ∀ i j l, i < j → j < l → l < n → l ≤ i + k →
      roundDist (phase (b i j) * phase (b j l)) (phase (b i l)) ≤ δ)
    {i j l : ℕ} (hij : i < j) (hjl : j < l) (hln : l < n) (hspan : l ≤ i + k) :
    forwardLift b i (j - i) + forwardLift b j (l - j) - forwardLift b i (l - i) =
      faceAngle b i j l := by
  generalize hd : l - i = d
  induction d using Nat.strong_induction_on generalizing i j l with
  | h d ih =>
    rw [forwardLift_step b hij, ← hd, forwardLift_step b (by omega : i < l)]
    by_cases he : j = i + 1
    · subst j
      simp [forwardLift, faceAngle]
    · have hp := ih (l - (i + 1)) (by omega) (by omega : i + 1 < j) hjl hln
        (by omega : l ≤ i + 1 + k) rfl
      have ht := faceAngle_tetra b hδ htri (by omega : i < i + 1)
        (by omega : i + 1 < j) hjl hln hspan
      linarith

/-- The antisymmetric real edge lift. -/
private def intervalLift (b : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i < j then forwardLift b i (j - i) else -forwardLift b j (i - j)

private theorem intervalLift_skew (b : ℕ → ℕ → ℝ) (i j : ℕ) :
    intervalLift b j i = -intervalLift b i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [intervalLift, h, h.not_gt]
  · simp [intervalLift, forwardLift]
  · simp [intervalLift, h, h.not_gt]

private theorem intervalLift_triangle {n k : ℕ} (b : ℕ → ℕ → ℝ) {δ : ℝ}
    (hδ : δ < π / 2)
    (htri : ∀ i j l, i < j → j < l → l < n → l ≤ i + k →
      roundDist (phase (b i j) * phase (b j l)) (phase (b i l)) ≤ δ)
    {i j l : ℕ} (hij : i < j) (hjl : j < l) (hln : l < n) (hspan : l ≤ i + k) :
    |intervalLift b i j + intervalLift b j l - intervalLift b i l| ≤ δ := by
  simp only [intervalLift, ite_eq_left hij, ite_eq_left hjl, ite_eq_left (hij.trans hjl)]
  rw [forwardLift_triangle b hδ htri hij hjl hln hspan]
  exact faceAngle_bound b htri hij hjl hln hspan

/-- Checking increasing triangles suffices for an antisymmetric real assignment. -/
private theorem triangle_bound_of_increasing {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (a : V → V → ℝ) (hskew : ∀ i j, a j i = -a i j) {δ : ℝ}
    (hinc : ∀ i j l, i < j → j < l → G.Adj i j → G.Adj j l → G.Adj i l →
      |a i j + a j l - a i l| ≤ δ) :
    ∀ i j l, G.Adj i j → G.Adj j l → G.Adj i l → |a i j + a j l - a i l| ≤ δ := by
  intro i j l hij hjl hil
  rcases lt_or_gt_of_ne hij.ne with h₁ | h₁
  · rcases lt_or_gt_of_ne hjl.ne with h₂ | h₂
    · exact hinc i j l h₁ h₂ hij hjl hil
    · rcases lt_or_gt_of_ne hil.ne with h₃ | h₃
      · have hh := hinc i l j h₃ h₂ hil hjl.symm hij
        rw [← abs_neg] at hh
        rw [hskew l j]
        convert hh using 1; congr 1; ring
      · have hh := hinc l i j h₃ h₁ hil.symm hij hjl.symm
        rw [hskew l j, hskew l i]
        convert hh using 1; congr 1; ring
  · rcases lt_or_gt_of_ne hil.ne with h₂ | h₂
    · have hh := hinc j i l h₁ h₂ hij.symm hil hjl
      rw [← abs_neg] at hh
      rw [hskew j i]
      convert hh using 1; congr 1; ring
    · rcases lt_or_gt_of_ne hjl.ne with h₃ | h₃
      · have hh := hinc j l i h₃ h₂ hjl hil.symm hij.symm
        rw [hskew j i, hskew l i]
        convert hh using 1; congr 1; ring
      · have hh := hinc l j i h₃ h₁ hjl.symm hij.symm hil.symm
        rw [← abs_neg] at hh
        rw [hskew j i, hskew l j, hskew l i]
        convert hh using 1; congr 1; ring

/-- Extend a finite array by zero solely to run the interval recursion. -/
private def natArray {n : ℕ} (b : Fin n → Fin n → ℝ) (i j : ℕ) : ℝ :=
  if hi : i < n then if hj : j < n then b ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

@[simp] theorem natArray_fin {n : ℕ} (b : Fin n → Fin n → ℝ) (i j : Fin n) :
    natArray b i.val j.val = b i j := by simp [natArray, i.isLt, j.isLt]

/-- Small-defect circle gains on a power path admit an actual real edge lift
whose triangle defects have the same bound. -/
private theorem powerPath_small_lift {n k : ℕ} (b : Fin n → Fin n → ℝ)
    (hrev : ∀ i j, (powerPath n k).Adj i j → phase (b j i) = (phase (b i j))⁻¹)
    {δ : ℝ} (hδ : δ < π / 2)
    (htri : TriangleBound (powerPath n k) (fun i j => phase (b i j)) δ) :
    ∃ a : Fin n → Fin n → ℝ,
      (∀ i j, a j i = -a i j) ∧
      (∀ i j, (powerPath n k).Adj i j → phase (a i j) = phase (b i j)) ∧
      (∀ i j l, (powerPath n k).Adj i j → (powerPath n k).Adj j l →
        (powerPath n k).Adj i l → |a i j + a j l - a i l| ≤ δ) := by
  let c := natArray b
  have hnat : ∀ i j l, i < j → j < l → l < n → l ≤ i + k →
      roundDist (phase (c i j) * phase (c j l)) (phase (c i l)) ≤ δ := by
    intro i j l hij hjl hln hs
    have hi : i < n := by omega
    have hj : j < n := by omega
    simpa [c, natArray, hi, hj, hln] using htri ⟨i, hi⟩ ⟨j, hj⟩ ⟨l, hln⟩
      ⟨by simp [Fin.ext_iff]; omega, by dsimp; omega, by dsimp; omega⟩
      ⟨by simp [Fin.ext_iff]; omega, by dsimp; omega, by dsimp; omega⟩
      ⟨by simp [Fin.ext_iff]; omega, by dsimp; omega, by dsimp; omega⟩
  let a (i j : Fin n) := intervalLift c i.val j.val
  have has : ∀ i j, a j i = -a i j := fun i j => intervalLift_skew c i.val j.val
  refine ⟨a, has, ?_, triangle_bound_of_increasing a has ?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij.ne with h | h
    · simpa [a, intervalLift, c, h] using forwardLift_phase c (show i.val < j.val from h)
    · rw [has j i, phase_neg]
      have hp : phase (a j i) = phase (b j i) := by
        simpa [a, intervalLift, c, h] using forwardLift_phase c (show j.val < i.val from h)
      rw [hp, hrev i j hij, inv_inv]
  · intro i j l hij hjl _ _ hil
    exact intervalLift_triangle c hδ hnat hij hjl l.isLt hil.2.2

/-- The least vertex of every induced subgraph of a path power is simplicial. -/
private theorem powerPath_chordal (n k : ℕ) : (powerPath n k).IsChordal := by
  classical
  let G := powerPath n k
  intro v c hc hlen
  obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image c.support.toFinset
    (fun x : Fin n => x.val) ⟨v, by simp⟩
  have hz' : z ∈ c.support := by simpa using hz
  let d := c.rotate z hz'
  have hd : d.IsCycle := hc.rotate hz'
  have hn : 4 ≤ d.length := by simpa [d] using hlen
  have he := c.rotate_edges z hz'
  have hsupp (w : Fin n) (hw : w ∈ d.support) : w ∈ c.support := by
    rw [← Walk.cons_tail_support] at hw
    rcases List.mem_cons.mp hw with rfl | hh
    · exact hz'
    · exact List.mem_of_mem_tail ((c.support_rotate z hz').mem_iff.mp hh)
  have hx := hsupp d.snd (d.getVert_mem_support 1)
  have hy := hsupp d.penultimate (d.getVert_mem_support (d.length - 1))
  have hzx := d.adj_snd hd.not_nil
  have hzy := (d.adj_penultimate hd.not_nil).symm
  have hminx := hmin d.snd (by simpa using hx)
  have hminy := hmin d.penultimate (by simpa using hy)
  have hxy : G.Adj d.snd d.penultimate := by
    refine ⟨hd.snd_ne_penultimate, ?_, ?_⟩
    · exact hzx.2.2.trans (Nat.add_le_add_right hminy k)
    · exact hzy.2.2.trans (Nat.add_le_add_right hminx k)
  refine ⟨d.snd, d.penultimate, hx, hy, hxy, ?_⟩
  intro hm
  have hmem : d.penultimate ∈ d.toSubgraph.neighborSet d.snd :=
    Walk.adj_toSubgraph_iff_mem_edges.mpr (he.mem_iff.mpr hm)
  change d.getVert (d.length - 1) ∈ d.toSubgraph.neighborSet (d.getVert 1) at hmem
  rw [hd.neighborSet_toSubgraph_internal (i := 1) (by omega) (by omega)] at hmem
  simp only [Nat.sub_self, Nat.reduceAdd, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have hfirst : d.length - 1 ∈ {i : ℕ | i ≤ d.length - 1} := by simp
  have hzero : 0 ∈ {i : ℕ | i ≤ d.length - 1} := by simp
  have htwo : 2 ∈ {i : ℕ | i ≤ d.length - 1} := by simp; omega
  rcases hmem with h | h
  · have eq := hd.getVert_injOn' hfirst hzero h
    omega
  · have eq := hd.getVert_injOn' hfirst htwo h
    omega

private theorem powerPath_small_defect {n k : ℕ} (b : Fin n → Fin n → ℝ)
    (hrev : ∀ i j, (powerPath n k).Adj i j → phase (b j i) = (phase (b i j))⁻¹)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ < π / 2)
    (htri : TriangleBound (powerPath n k) (fun i j => phase (b i j)) δ) :
    ∃ p : Fin n → U, Fits (powerPath n k) (fun i j => phase (b i j)) p δ := by
  obtain ⟨a, has, hap, hat⟩ := powerPath_small_lift b hrev hsmall htri
  obtain ⟨p, hp⟩ := fit_of_real_lift (powerPath_chordal n k) a
    (fun i j _ => has i j) hδ hat
  exact ⟨p, fun i j hij => by simpa [hap i j hij] using hp i j hij⟩

/-- The large- and small-defect constructions give one for every width. -/
private theorem powerPath_phase_coefficient_one {n k : ℕ} (b : Fin n → Fin n → ℝ)
    (hdiag : ∀ i, phase (b i i) = 1)
    (hrev : ∀ i j, (powerPath n k).Adj i j → phase (b j i) = (phase (b i j))⁻¹)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (htri : TriangleBound (powerPath n k) (fun i j => phase (b i j)) δ) :
    ∃ p : Fin n → U, Fits (powerPath n k) (fun i j => phase (b i j)) p δ := by
  by_cases hk : k = 0
  · subst k
    exact ⟨fun _ => 1, fun i j hij => (hij.1 (Fin.ext (by have h₁ := hij.2.1; have h₂ := hij.2.2; omega))).elim⟩
  · by_cases hsmall : δ < π / 2
    · exact powerPath_small_defect b hrev hδ hsmall htri
    · exact powerPath_large_defect (Nat.pos_of_ne_zero hk) b hdiag hrev
        (le_of_not_gt hsmall) htri

/-- Every circle-supported assignment on every finite path power admits a fit
in the full unit-quaternion target with error at most its triangle bound.
There is no bound on clique size or path-power width. -/
theorem powerPath_circle_coefficient_one {n k : ℕ} (g : Fin n → Fin n → U)
    (hcircle : ∀ i j, (powerPath n k).Adj i j → ∃ t : ℝ, phase t = g i j)
    (hrev : ∀ i j, (powerPath n k).Adj i j → g j i = (g i j)⁻¹)
    {δ : ℝ} (hδ : 0 ≤ δ) (htri : TriangleBound (powerPath n k) g δ) :
    ∃ p : Fin n → U, Fits (powerPath n k) g p δ := by
  classical
  let b (i j : Fin n) : ℝ := if h : (powerPath n k).Adj i j then (hcircle i j h).choose else 0
  have hb (i j : Fin n) (hij : (powerPath n k).Adj i j) : phase (b i j) = g i j := by
    simp only [b, dite_eq_left hij]
    exact (hcircle i j hij).choose_spec
  have hd (i : Fin n) : phase (b i i) = 1 := by simp [b]
  have hr (i j : Fin n) (hij : (powerPath n k).Adj i j) :
      phase (b j i) = (phase (b i j))⁻¹ := by rw [hb j i hij.symm, hb i j hij, hrev i j hij]
  have ht : TriangleBound (powerPath n k) (fun i j => phase (b i j)) δ := by
    intro i j l hij hjl hil
    simpa [hb i j hij, hb j l hjl, hb i l hil] using htri i j l hij hjl hil
  obtain ⟨p, hp⟩ := powerPath_phase_coefficient_one b hd hr hδ ht
  exact ⟨p, fun i j hij => by simpa [hb i j hij] using hp i j hij⟩

/-- The cycle lower bound allows arbitrary ambient quaternion potentials. -/
private theorem walk_fit_bound (g : V → V → U) (p : V → U) {E : ℝ}
    (hfit : Fits G g p E) {a b : V} (w : G.Walk a b) :
    roundDist (w.gain g) ((p a)⁻¹ * p b) ≤ (w.length : ℝ) * E := by
  induction w with
  | nil => simp
  | @cons a x b h w ih =>
    have ht := round_triangle (g a x * w.gain g)
      (g a x * ((p x)⁻¹ * p b)) (((p a)⁻¹ * p x) * ((p x)⁻¹ * p b))
    rw [round_mul_left, round_mul_right] at ht
    have he : ((p a)⁻¹ * p x) * ((p x)⁻¹ * p b) = (p a)⁻¹ * p b := by group
    rw [he] at ht
    simp only [Walk.gain_cons, Walk.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith [hfit a x h]

private theorem walk_gain_phase (b : V → V → ℝ) {a c : V} (w : G.Walk a c) :
    w.gain (fun i j => phase (b i j)) = phase (w.scalarWeight b) := by
  induction w with
  | nil => simp
  | cons h w ih => simp [ih, phase_add]

private def along (f : ℕ → V) : (m : ℕ) → (∀ r, r < m → G.Adj (f r) (f (r + 1))) →
    G.Walk (f 0) (f m)
  | 0, _ => .nil
  | m + 1, h => (along f m (fun r hr => h r (by omega))).concat (h m (by omega))

@[simp] theorem along_length (f : ℕ → V) (m : ℕ)
    (h : ∀ r, r < m → G.Adj (f r) (f (r + 1))) : (along f m h).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [along, ih]

private theorem along_weight (f : ℕ → V) (m : ℕ)
    (h : ∀ r, r < m → G.Adj (f r) (f (r + 1))) (b : V → V → ℝ) (c : ℝ)
    (hb : ∀ r, r < m → b (f r) (f (r + 1)) = c) :
    (along f m h).scalarWeight b = (m : ℝ) * c := by
  induction m with
  | zero => simp [along]
  | succ m ih =>
    simp [along, Walk.concat, ih _ (fun r hr => hb r (by omega)), hb m (by omega), add_mul]

private def sharpSign (i : ℕ) : ℝ := if i % 2 = 0 then 1 else -1
private def sharpForward (i j : ℕ) : ℝ :=
  if j = i + 1 then -sharpSign i / 2 else if j = i + 2 then sharpSign i else 0
private def sharpA (i j : ℕ) : ℝ := if i < j then sharpForward i j else -sharpForward j i

private theorem sharpA_skew (i j : ℕ) : sharpA j i = -sharpA i j := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [sharpA, h, h.not_gt]
  · simp [sharpA, sharpForward]
  · simp [sharpA, h, h.not_gt]

private theorem sharpA_triangle {n : ℕ} :
    ∀ i j l : Fin n, (powerPath n 2).Adj i j → (powerPath n 2).Adj j l →
      (powerPath n 2).Adj i l → |sharpA i.val j.val + sharpA j.val l.val - sharpA i.val l.val| ≤ 1 := by
  apply triangle_bound_of_increasing (fun i j : Fin n => sharpA i.val j.val) (fun i j => sharpA_skew _ _)
  intro i j l hij hjl _ _ hil
  have h₁ : j.val = i.val + 1 := by have := hil.2.2; omega
  have h₂ : l.val = i.val + 2 := by have := hil.2.2; omega
  have hi : i.val % 2 < 2 := Nat.mod_lt _ (by decide)
  have hj : (i.val + 1) % 2 = 1 - i.val % 2 := by omega
  simp [sharpA, sharpForward, h₁, h₂, sharpSign, hj]
  split_ifs <;> norm_num <;> omega

private def evenV (L r : ℕ) : Fin (2 * L + 2) := ⟨2 * min r L, by have := min_le_right r L; omega⟩
private def oddV (L r : ℕ) : Fin (2 * L + 2) := ⟨2 * (L - r) + 1, by omega⟩

private theorem even_adj (L r : ℕ) (hr : r < L) :
    (powerPath (2 * L + 2) 2).Adj (evenV L r) (evenV L (r + 1)) := by
  simp only [BanachPathPower.pathPower, evenV, min_eq_left hr.le, min_eq_left (by omega : r + 1 ≤ L)]
  refine ⟨by simp [Fin.ext_iff], ?_, ?_⟩ <;> omega

private theorem odd_adj (L r : ℕ) (hr : r < L) :
    (powerPath (2 * L + 2) 2).Adj (oddV L r) (oddV L (r + 1)) := by
  refine ⟨by simp [oddV, Fin.ext_iff]; omega, ?_, ?_⟩ <;> dsimp [oddV] <;> omega

private theorem bridge_adj (L : ℕ) :
    (powerPath (2 * L + 2) 2).Adj (evenV L L) (oddV L 0) := by
  refine ⟨by simp [evenV, oddV], ?_, ?_⟩ <;>
    simp [evenV, oddV]
  omega

private theorem close_adj (L : ℕ) :
    (powerPath (2 * L + 2) 2).Adj (oddV L L) (evenV L 0) := by
  refine ⟨by simp [evenV, oddV], ?_, ?_⟩ <;> simp [evenV, oddV]

/-- The cycle `0,2,...,2L,2L+1,2L-1,...,1,0`. -/
private def sharpWalk (L : ℕ) : (powerPath (2 * L + 2) 2).Walk (evenV L 0) (evenV L 0) :=
  (((along (evenV L) L (even_adj L)).concat (bridge_adj L)).append
    (along (oddV L) L (odd_adj L))).concat (close_adj L)

@[simp] theorem sharpWalk_length (L : ℕ) : (sharpWalk L).length = 2 * L + 2 := by
  simp [sharpWalk]
  omega

private theorem sharpWalk_weight (L : ℕ) :
    (sharpWalk L).scalarWeight (fun i j => sharpA i.val j.val) = 2 * L := by
  have he : ∀ r, r < L → sharpA (evenV L r).val (evenV L (r + 1)).val = 1 := by
    intro r hr
    simp [evenV, min_eq_left hr.le, min_eq_left (by omega : r + 1 ≤ L),
      sharpA, sharpForward, sharpSign, show 2 * (r + 1) = 2 * r + 2 by omega]
  have ho : ∀ r, r < L → sharpA (oddV L r).val (oddV L (r + 1)).val = 1 := by
    intro r hr
    have hh : L - r = L - (r + 1) + 1 := by omega
    simp [oddV, hh, sharpA, sharpForward, sharpSign, Nat.add_mod,
      show 2 * (L - (r + 1) + 1) = 2 * (L - (r + 1)) + 2 by omega]
  have hb : sharpA (evenV L L).val (oddV L 0).val = -(1 / 2 : ℝ) := by
    norm_num [evenV, oddV, sharpA, sharpForward, sharpSign, Nat.add_mod, Nat.mul_mod]
  have hc : sharpA (oddV L L).val (evenV L 0).val = (1 / 2 : ℝ) := by
    norm_num [evenV, oddV, sharpA, sharpForward, sharpSign]
  simp [sharpWalk, Walk.concat, along_weight (evenV L) L (even_adj L) (fun i j => sharpA i.val j.val) 1 he,
    along_weight (oddV L) L (odd_adj L) (fun i j => sharpA i.val j.val) 1 ho, hb, hc]
  ring

def sharpEpsilon (L : ℕ) : ℝ := π / (4 * L)
def sharpGain (L : ℕ) (i j : Fin (2 * L + 2)) : U :=
  phase (sharpEpsilon L * sharpA i.val j.val)

private theorem sharpEpsilon_pos {L : ℕ} (hL : 0 < L) : 0 < sharpEpsilon L := by
  exact div_pos pi_pos (by exact_mod_cast (show 0 < 4 * L by omega))

private theorem sharpEpsilon_le_pi {L : ℕ} (hL : 0 < L) : sharpEpsilon L ≤ π := by
  dsimp [sharpEpsilon]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * L)).mpr
  have hl : (1 : ℝ) ≤ L := by exact_mod_cast hL
  nlinarith [pi_pos]

private theorem sharpGain_skew (L : ℕ) (i j : Fin (2 * L + 2)) :
    sharpGain L j i = (sharpGain L i j)⁻¹ := by
  simp [sharpGain, sharpA_skew i.val j.val, ← phase_neg]

private theorem sharpGain_triangle {L : ℕ} (hL : 0 < L) :
    TriangleBound (powerPath (2 * L + 2) 2) (sharpGain L) (sharpEpsilon L) := by
  intro i j l hij hjl hil
  have hh := sharpA_triangle i j l hij hjl hil
  change roundDist (phase _ * phase _) (phase _) ≤ _
  rw [← phase_add]
  apply (phase_dist_le _ _).trans
  have he : sharpEpsilon L * sharpA i.val j.val + sharpEpsilon L * sharpA j.val l.val -
      sharpEpsilon L * sharpA i.val l.val =
      sharpEpsilon L * (sharpA i.val j.val + sharpA j.val l.val - sharpA i.val l.val) := by ring
  rw [he, abs_mul, abs_of_pos (sharpEpsilon_pos hL)]
  exact (mul_le_mul_of_nonneg_left hh (sharpEpsilon_pos hL).le).trans_eq (mul_one _)

private theorem scalarWeight_mul (b : V → V → ℝ) (t : ℝ) {a c : V} (w : G.Walk a c) :
    w.scalarWeight (fun i j => t * b i j) = t * w.scalarWeight b := by
  induction w with
  | nil => simp
  | cons h w ih => simp [ih, mul_add]

private theorem sharp_scale {L : ℕ} (hL : 0 < L) : (2 * L : ℝ) * sharpEpsilon L = π / 2 := by
  have hl : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  dsimp [sharpEpsilon]
  field_simp
  ring

/-- The displayed cycle has quarter-turn holonomy for every positive `L`. -/
private theorem sharpWalk_holonomy {L : ℕ} (hL : 0 < L) :
    roundDist ((sharpWalk L).gain (sharpGain L)) 1 = π / 2 := by
  rw [show sharpGain L = (fun i j => phase (sharpEpsilon L * sharpA i.val j.val)) from rfl,
    walk_gain_phase, scalarWeight_mul, sharpWalk_weight, mul_comm (sharpEpsilon L), sharp_scale hL,
    ← phase_zero, phase_dist_exact (by rw [sub_zero, abs_of_nonneg (by positivity)]; linarith [pi_pos])]
  rw [sub_zero, abs_of_nonneg (by positivity)]

/-- Exact finite ambient obstruction: every fit has ratio at least `L / (L + 1)`. -/
theorem sharpGain_ambient_lower {L : ℕ} (hL : 0 < L) (p : Fin (2 * L + 2) → U)
    {E : ℝ} (hfit : Fits (powerPath (2 * L + 2) 2) (sharpGain L) p E) :
    sharpEpsilon L * L / (L + 1) ≤ E := by
  have hb := walk_fit_bound (sharpGain L) p hfit (sharpWalk L)
  rw [inv_mul_cancel, sharpWalk_holonomy hL, sharpWalk_length] at hb
  have hs := sharp_scale hL
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < L + 1)).mpr
  push_cast at hb
  nlinarith

/-- The triangle at `0,1,2` attains the defect; the normalization is exact. -/
theorem sharpGain_exact_defect {L : ℕ} (hL : 0 < L) :
    TriangleBound (powerPath (2 * L + 2) 2) (sharpGain L) (sharpEpsilon L) ∧
    ∃ i j l : Fin (2 * L + 2), (powerPath (2 * L + 2) 2).Adj i j ∧
      (powerPath (2 * L + 2) 2).Adj j l ∧ (powerPath (2 * L + 2) 2).Adj i l ∧
      roundDist (sharpGain L i j * sharpGain L j l) (sharpGain L i l) = sharpEpsilon L := by
  refine ⟨sharpGain_triangle hL, ⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩,
    ⟨by simp, by norm_num, by norm_num⟩, ⟨by simp, by norm_num, by norm_num⟩,
    ⟨by simp, by norm_num, by norm_num⟩, ?_⟩
  norm_num [sharpGain, sharpA, sharpForward, sharpSign]
  rw [← phase_zero, phase_dist_exact (by
    rw [zero_sub, abs_neg, abs_of_pos (sharpEpsilon_pos hL)]
    exact sharpEpsilon_le_pi hL)]
  simp [abs_of_pos (sharpEpsilon_pos hL)]

/-- No coefficient below one works on all finite width-two examples. -/
private theorem coefficient_below_one_fails {C : ℝ} (hC : C < 1) :
    ∃ L : ℕ, 0 < L ∧ ∀ p : Fin (2 * L + 2) → U,
      ¬ Fits (powerPath (2 * L + 2) 2) (sharpGain L) p (C * sharpEpsilon L) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - C))
  let L := m + 1
  have hL : 0 < L := by omega
  have hd : 0 < 1 - C := by linarith
  have hm' : 1 < (m : ℝ) * (1 - C) := (div_lt_iff₀ hd).mp hm
  have hratio : C * ((L : ℝ) + 1) < L := by dsimp [L]; push_cast; nlinarith
  refine ⟨L, hL, fun p hp => ?_⟩
  have hb := sharpGain_ambient_lower hL p hp
  have he := sharpEpsilon_pos hL
  have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < L + 1)).mp hb
  nlinarith

/-- A uniform ambient coefficient, quantified over every finite order and every
path-power width. Circle support constrains gains; potentials range over all `U`. -/
def Admissible (C : ℝ) : Prop :=
  ∀ (n k : ℕ) (g : Fin n → Fin n → U),
    (∀ i j, (powerPath n k).Adj i j → ∃ t : ℝ, phase t = g i j) →
    (∀ i j, (powerPath n k).Adj i j → g j i = (g i j)⁻¹) →
    ∀ δ : ℝ, 0 ≤ δ → TriangleBound (powerPath n k) g δ →
      ∃ p : Fin n → U, Fits (powerPath n k) g p (C * δ)

/-- The optimal uniform ambient coefficient on the width-unrestricted power-path
family is exactly one. Both the upper bound and the finite sharpness family
allow the fitting potential to range over the whole round unit-quaternion group. -/
theorem admissible_iff_one_le (C : ℝ) : Admissible C ↔ 1 ≤ C := by
  constructor
  · intro h
    by_contra! hC
    obtain ⟨L, hL, hf⟩ := coefficient_below_one_fails hC
    obtain ⟨p, hp⟩ := h (2 * L + 2) 2 (sharpGain L)
      (fun i j _ => ⟨sharpEpsilon L * sharpA i.val j.val, rfl⟩)
      (fun i j _ => sharpGain_skew L i j) (sharpEpsilon L)
      (sharpEpsilon_pos hL).le (sharpGain_triangle hL)
    exact hf p hp
  · intro hC n k g hc hr δ hδ ht
    obtain ⟨p, hp⟩ := powerPath_circle_coefficient_one g hc hr hδ ht
    refine ⟨p, fun i j hij => (hp i j hij).trans ?_⟩
    simpa using mul_le_mul_of_nonneg_right hC hδ

end SimpleGraph.CirclePowerPath
