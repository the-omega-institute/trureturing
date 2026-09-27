/- GID: D5/S1/Words/HughesIterationDepthNoGap
   generality: G
   mirror-B: D5/B/S1/Words/HughesIterationDepthNoGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The minimum iteration-depth spectrum of literal fixed-degree insertion has no gaps. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.HughesIterationDepthNoGap

abbrev Language (α : Type*) := Set (List α)

private def pairOutput {α : Type*} (pieces : List (List α × List α)) (tail : List α) : List α :=
  (pieces.map (fun p => p.1 ++ p.2)).flatten ++ tail

private def baseWord {α : Type*} (pieces : List (List α × List α)) (tail : List α) : List α :=
  (pieces.map Prod.fst).flatten ++ tail

private def sourceWord {α : Type*} (pieces : List (List α × List α)) : List α :=
  (pieces.map Prod.snd).flatten

/-- The literal degree-k insertion operation from the source definition. -/
def fixedDegreeInsertion {α : Type*} (k : Nat) (A B : Language α) : Language α :=
  {w | ∃ pieces : List (List α × List α), pieces.length = k ∧
      ∃ tail : List α, baseWord pieces tail ∈ B ∧ sourceWord pieces ∈ A ∧
        pairOutput pieces tail = w}

/-- Iteration with one fixed positive insertion degree throughout the history. -/
def fixedDegreeIterate {α : Type*} (k : Nat) (A B : Language α) : Nat → Language α
  | 0 => B
  | m + 1 => fixedDegreeInsertion k A (fixedDegreeIterate k A B m)

/-- A word appears at a given stage for some positive fixed degree. -/
def appearsAt {α : Type*} (A B : Language α) (w : List α) (m : Nat) : Prop :=
  ∃ k, 0 < k ∧ w ∈ fixedDegreeIterate k A B m

/-- A word has minimum iteration depth m. -/
def hasIterationDepth {α : Type*} (A B : Language α) (w : List α) (m : Nat) : Prop :=
  appearsAt A B w m ∧ ∀ n < m, ¬ appearsAt A B w n

/-- The iteration-depth spectrum, retaining exactly the attained minimum depths. -/
def iterationDepthSpectrum {α : Type*} (A B : Language α) : Set Nat :=
  {m | ∃ w, hasIterationDepth A B w m}

/-- The source convention measures actual iteration depth from zero. -/
def closedSourceZero : Fin 2 := 0

/-- Re-express the actual spectrum in the coordinate selected by an origin. -/
def iterationDepthSpectrumAt {α : Type*} (origin : Fin 2) (A B : Language α) : Set Nat :=
  {n | ∃ m, m ∈ iterationDepthSpectrum A B ∧ n = m + origin.val}

private theorem fixedDegreeInsertion_degree_mono {α : Type*} {A B : Language α}
    {j K : Nat} (h : j ≤ K) {w : List α} (hw : w ∈ fixedDegreeInsertion j A B) :
    w ∈ fixedDegreeInsertion K A B := by
  rcases hw with ⟨pieces, hpieces, tail, hbase, hsource, hout⟩
  let extra : List (List α × List α) := List.replicate (K - j) ([], [])
  refine ⟨pieces ++ extra, ?_, tail, ?_, ?_, ?_⟩
  · rw [List.length_append, hpieces, List.length_replicate]
    exact Nat.add_sub_of_le h
  · simpa [baseWord, extra, List.map_append, List.flatten_append, hpieces, Nat.sub_add_cancel h]
      using hbase
  · simpa [sourceWord, extra, List.map_append, List.flatten_append] using hsource
  · simpa [pairOutput, extra, List.map_append, List.flatten_append] using hout

private theorem fixedDegreeIterate_degree_mono {α : Type*} {A B : Language α}
    {j K m : Nat} (h : j ≤ K) {w : List α}
    (hw : w ∈ fixedDegreeIterate j A B m) :
    w ∈ fixedDegreeIterate K A B m := by
  induction m generalizing j K w with
  | zero => simpa [fixedDegreeIterate] using hw
  | succ m ih =>
      have hcur : w ∈ fixedDegreeInsertion j A (fixedDegreeIterate j A B m) := by
        simpa [fixedDegreeIterate] using hw
      rcases hcur with ⟨pieces, hpieces, tail, hbase, hsource, hout⟩
      have hbaseK : baseWord pieces tail ∈ fixedDegreeIterate K A B m :=
        ih h (by simpa [fixedDegreeIterate] using hbase)
      have hcurK : w ∈ fixedDegreeInsertion j A (fixedDegreeIterate K A B m) :=
        ⟨pieces, hpieces, tail, hbaseK, hsource, hout⟩
      exact fixedDegreeInsertion_degree_mono h hcurK

private theorem insertion_predecessor_depth {α : Type*}
    {A B : Language α} {w : List α} {r k : Nat}
    (hk : 0 < k) (hw : w ∈ fixedDegreeIterate k A B (r + 1))
    (hmin : ∀ n < r + 1, ¬ appearsAt A B w n) :
    ∃ v, v ∈ fixedDegreeIterate k A B r ∧ hasIterationDepth A B v r := by
  rcases hw with ⟨pieces, hpieces, tail, hv, hy, hout⟩
  let v := baseWord pieces tail
  have hv_mem : v ∈ fixedDegreeIterate k A B r := by
    simpa [v, fixedDegreeIterate] using hv
  have hv_depth : hasIterationDepth A B v r := by
    refine ⟨⟨k, hk, hv_mem⟩, ?_⟩
    intro s hs hvs
    rcases hvs with ⟨j, hj, hvs⟩
    let K := max k j
    have hKk : k ≤ K := Nat.le_max_left _ _
    have hKj : j ≤ K := Nat.le_max_right _ _
    have hvsK : v ∈ fixedDegreeIterate K A B s :=
      fixedDegreeIterate_degree_mono hKj hvs
    have hpadk : w ∈ fixedDegreeInsertion k A (fixedDegreeIterate K A B s) := by
      refine ⟨pieces, hpieces, tail, ?_, hy, hout⟩
      simpa [v] using hvsK
    have hpad : w ∈ fixedDegreeInsertion K A (fixedDegreeIterate K A B s) :=
      fixedDegreeInsertion_degree_mono hKk hpadk
    have hnext : w ∈ fixedDegreeIterate K A B (s + 1) := by
      simpa [fixedDegreeIterate] using hpad
    exact hmin (s + 1) (by omega) ⟨K, Nat.pos_of_ne_zero (by omega), hnext⟩
  exact ⟨v, hv_mem, hv_depth⟩

private theorem spectrum_downward_step {α : Type*}
    {A B : Language α} {r : Nat} (hr : r + 1 ∈ iterationDepthSpectrum A B) :
    r ∈ iterationDepthSpectrum A B := by
  rcases hr with ⟨w, hw⟩
  rcases hw with ⟨hw_app, hw_min⟩
  rcases hw_app with ⟨k, hk, hwk⟩
  rcases insertion_predecessor_depth hk hwk hw_min with ⟨v, _, hv⟩
  exact ⟨v, hv⟩

private theorem spectrum_downward_closure {α : Type*}
    {A B : Language α} : ∀ r, r ∈ iterationDepthSpectrum A B →
      ∀ q, q ≤ r → q ∈ iterationDepthSpectrum A B
  | 0, hr, 0, _ => hr
  | r + 1, hr, q, hq => by
      have hprev : r ∈ iterationDepthSpectrum A B := spectrum_downward_step hr
      rcases hq.eq_or_lt with rfl | hlt
      · exact hr
      · exact spectrum_downward_closure r hprev q (Nat.lt_succ_iff.mp hlt)

/- The source's arbitrary-language iteration-depth no-gap conjecture. -/
theorem result (α : Type) [Finite α]
    (A B : Language α) (r : Nat)
    (hr : r ∈ iterationDepthSpectrumAt closedSourceZero A B) :
    ∀ q ≤ r, q ∈ iterationDepthSpectrumAt closedSourceZero A B := by
  simpa [iterationDepthSpectrumAt, closedSourceZero] using
    spectrum_downward_closure (A := A) (B := B) r (by
      simpa [iterationDepthSpectrumAt, closedSourceZero] using hr)

end D5.S1.Words.HughesIterationDepthNoGap
