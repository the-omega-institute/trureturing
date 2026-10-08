/- GID: D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Section 6 construction and its triangular reduction. -/

/- Judgement form (implementation assessment; each helper retains its own classification).
   proof_shape: Draft.triangular_pivot: content.
   proof_shape: Spectral.det_pencil: bind-only; consumer=UniformParameterAnchor.Uniform.pencil_top_largest.
   proof_shape: Spectral.pencil_conjugate: bind-only; consumer=ConstructionReduction.Spectral.largest_root_psd.
   proof_shape: Spectral.largest_root_psd: bind-only; consumer=UniformPerturbedParameters.Anchor.largest_root_psd.
   proof_shape: Spectral.det_pencil_re: bind-only; consumer=UniformParameterAnchor.Uniform.simple_root_of_rank.
   proof_shape: D_hermitian: bind-only; consumer=UniformPerturbedParameters.Anchor.largest_root_psd.
   proof_shape: D_pencil: bind-only; consumer=UniformPerturbedParameters.Anchor.largest_root_psd.
   proof_shape: partialTranspose_involutive: bind-only; consumer=ConstructionReduction.proposition61.
   proof_shape: Path.scaled_dominance_posDef: bind-only; consumer=UniformParameterAnchor.Anchor.interior_posDef.
   proof_shape: Path.sum_indicator_le: bind-only; consumer=UniformParameterAnchor.Uniform.band_spike_dominance.
   proof_shape: proposition61: content.
   escape_witness: Draft.triangular_pivot, on proposition61’s triangular support-classification path.
   admission_basis: escape-witness
   Direct frozen dependencies:
   D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.partialTransposeB; statement_id=sha256:894491a0350c31f846bcfc59cbb3e13f12eb0801f6a00517db381f0dc0ecc393
   Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.LinearAlgebra.Matrix.Gershgorin

noncomputable section
namespace D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
open scoped ComplexConjugate ComplexOrder
def phaseAt {n : ℕ} (a : Fin n → ℂ) (j : ℕ) : ℂ := if h : j - 1 < n then a ⟨j - 1, h⟩ else 1
def pEntry (d : ℕ) (z : ℕ → ℂ) (i j : ℕ) : ℂ := if i = j then (if d = 2 then 1 else 2) else if j = i + 1 then z j / z i else if i = j + 1 then z j / z i else if i = 0 ∧ j + 1 = d then z j else if j = 0 ∧ i + 1 = d then (z i)⁻¹ else 0
def P (d : ℕ) (z : ℕ → ℂ) : Matrix (Fin d) (Fin d) ℂ := fun i j => pEntry d z i.val j.val
def alphaUpper (k : ℕ) : List (ℕ × ℕ) := (List.range (k / 2)).map fun j => (j + 1, k - j)
def betaUpper (n l : ℕ) : List (ℕ × ℕ) := (List.range ((n - l + 1) / 2)).map fun j => (l + j, n - j)
def indexList (upper : List (ℕ × ℕ)) : List (ℕ × ℕ) := upper ++ upper.reverse.map Prod.swap
def blockZ {n : ℕ} (a : Fin n → ℂ) (upper : List (ℕ × ℕ)) (j : ℕ) : ℂ := if j < upper.length then 1 else match (indexList upper)[j]? with | some p => (phaseAt a p.2)⁻¹ * phaseAt a p.1 | none => 1
def blockEntry {n : ℕ} (a : Fin n → ℂ) (upper : List (ℕ × ℕ)) (scale : ℂ) (row col : (Fin n × Fin n)) : ℂ := let indices := indexList upper; let rr := (row.1.val + 1, row.2.val + 1); let cc := (col.1.val + 1, col.2.val + 1); if rr ∈ indices ∧ cc ∈ indices then scale * pEntry indices.length (blockZ a upper) (indices.idxOf rr) (indices.idxOf cc) else 0
def rhoGamma {n : ℕ} (a b : Fin n → ℂ) (r : ℝ) : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) := fun row col => (if row.1 = row.2 ∧ row = col then (r : ℂ) else 0) + blockEntry a [(1, 2)] 1 row col + blockEntry a [(1, 3)] 2 row col + (∑ k ∈ Finset.range (n + 1), if 4 ≤ k then blockEntry a (alphaUpper k) 1 row col else 0) + (∑ l ∈ Finset.range (n + 1), if 2 ≤ l ∧ l + 3 ≤ n then blockEntry b (betaUpper n l) 1 row col else 0) + (if 3 < n then blockEntry b [(n - 2, n)] 2 row col else 0) + blockEntry b [(n - 1, n)] 1 row col
def partialTranspose {n : ℕ} (A : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) := D5.S3.Quantum.Entanglement.StructuredNegativityCoincidenceRefutation.partialTransposeB A.transpose
def rho {n : ℕ} (a b : Fin n → ℂ) (r : ℝ) : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) := partialTranspose (rhoGamma a b r)
def D {n : ℕ} (a b : Fin n → ℂ) (r : ℝ) : Matrix (Fin n) (Fin n) ℂ := fun i j => if i = j then (r : ℂ) else if i.val = 0 then (if j.val = 2 then 2 else 1) * conj (a j) else if j.val = 0 then (if i.val = 2 then 2 else 1) * a i else if j.val + 1 = n then (if i.val + 3 = n then 2 else 1) * b i else if i.val + 1 = n then (if j.val + 3 = n then 2 else 1) * conj (b j) else if i.val + 1 = j.val ∨ j.val + 1 = i.val ∨ i.val + 2 = j.val ∨ j.val + 2 = i.val then if i.val + j.val + 1 ≤ n then a i * conj (a j) else b i * conj (b j) else 0
def tensor {n : ℕ} (x y : Fin n → ℂ) : (Fin n × Fin n) → ℂ := fun ij => Matrix.vecMulVec x y ij.1 ij.2
def InRange {n : ℕ} (A : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) (v : (Fin n × Fin n) → ℂ) : Prop := v ∈ LinearMap.range A.mulVecLin
def PPT {n : ℕ} (A : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) : Prop := A.PosSemidef ∧ (partialTranspose A).PosSemidef
def Edge {n : ℕ} (A : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) : Prop := ∀ x y : Fin n → ℂ, x ≠ 0 → y ≠ 0 → ¬ (InRange A (tensor x y) ∧ InRange (partialTranspose A) (tensor (fun i => conj (x i)) y))
def GenericPhases {n : ℕ} (a b : Fin n → ℂ) : Prop := (∀ i, a i ≠ 0 ∧ b i ≠ 0) ∧ ∀ i j : Fin n, i < j → (a i)⁻¹ * a j ≠ (b i)⁻¹ * b j
def Admissible {n : ℕ} (a b : Fin n → ℂ) : Prop := (∀ i, ‖a i‖ = 1 ∧ ‖b i‖ = 1) ∧ phaseAt a 1 = 1 ∧ phaseAt b n = 1 ∧ ∀ i j : Fin n, i < j → (a i)⁻¹ * a j ≠ (b i)⁻¹ * b j
def LargestRoot {n : ℕ} (a b : Fin n → ℂ) (r : ℝ) : Prop := (D a b r).det = 0 ∧ ∀ s : ℝ, (D a b s).det = 0 → s ≤ r
def SimpleRoot {n : ℕ} (a b : Fin n → ℂ) (r : ℝ) : Prop := ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt (fun s : ℝ => (D a b s).det.re) d r
def bracket {n : ℕ} (a x y : Fin n → ℂ) (i j : ℕ) : ℂ := phaseAt x i * phaseAt y j - (phaseAt a i)⁻¹ * phaseAt a j * phaseAt x j * phaseAt y i
def BilinearSystem {n : ℕ} (a b x y : Fin n → ℂ) : Prop := (∀ k ∈ Finset.Icc 2 n, ∑ j ∈ Finset.range (k / 2), (-1 : ℂ)^j * bracket a x y (j+1) (k-j) = 0) ∧ (∀ l ∈ Finset.Icc 1 (n-2), ∑ j ∈ Finset.range ((l+1)/2), (-1 : ℂ)^j * bracket b x y (n-l+j) (n-j) = 0)
def AllowedSupport (n : ℕ) (isAlpha : Bool) (s : Finset (Fin n)) : Prop := if isAlpha then (∀ i ∈ s, 2*(i.val+1) ≤ n+1) ∨ ∃ p q : Fin n, p ∈ s ∧ q ∈ s ∧ p.val+q.val+2 ≤ n+1 ∧ 2*(p.val+1) < n+1 ∧ n+1 < 2*(q.val+1) ∧ ∀ i ∈ s, i = q ∨ (p ≤ i ∧ i.val+q.val+2 ≤ n+1) else (∀ i ∈ s, n+1 ≤ 2*(i.val+1)) ∨ ∃ p q : Fin n, p ∈ s ∧ q ∈ s ∧ n+1 < p.val+q.val+2 ∧ 2*(p.val+1) < n+1 ∧ n+1 < 2*(q.val+1) ∧ ∀ i ∈ s, i = p ∨ (n+1 < i.val+p.val+2 ∧ i ≤ q)
def Classified {n : ℕ} (a b x y : Fin n → ℂ) : Prop := x = 0 ∨ y = 0 ∨ ∃ (isAlpha : Bool) (s : Finset (Fin n)) (c : Fin n → ℂ) (t : ℂ), t ≠ 0 ∧ s.Nonempty ∧ AllowedSupport n isAlpha s ∧ (∀ i, c i ≠ 0 ↔ i ∈ s) ∧ (∀ i, x i = c i * t ∧ y i = c i * (if isAlpha then a i else b i))
def StarCondition {n : ℕ} (a b w : Fin n → ℂ) : Prop := ∀ (isAlpha : Bool) (s : Finset (Fin n)), s.Nonempty → AllowedSupport n isAlpha s → ∀ u : Fin n → ℝ, (∀ i, 0 ≤ u i) → (∀ i, u i ≠ 0 ↔ i ∈ s) → (∑ i, ((u i : ℂ) * (if isAlpha then a i else b i)) * conj (w i)) ≠ 0
private def lemma33_statement : Prop := ∀ n : ℕ, 3 ≤ n → ∀ a b x y : Fin n → ℂ, GenericPhases a b → BilinearSystem a b x y → Classified a b x y
private def range_reduction_statement : Prop := ∀ n : ℕ, 3 ≤ n → ∀ (a b x y : Fin n → ℂ) (r : ℝ), Admissible a b → 1 < r → (InRange (rhoGamma a b r) (tensor (fun i => conj (x i)) y) ↔ BilinearSystem a b (fun i => conj (x i)) y)
def proposition61_statement : Prop := ∀ n : ℕ, 3 ≤ n → ∀ (a b : Fin n → ℂ) (r : ℝ) (w : Fin n → ℂ), Admissible a b → 1 < r → LargestRoot a b r → SimpleRoot a b r → w ≠ 0 → (D a b r).mulVec w = 0 → StarCondition a b w → PPT (rho a b r) ∧ Edge (rho a b r) ∧ Matrix.rank (rho a b r) = n*n-1 ∧ Matrix.rank (rhoGamma a b r) = n*n-2*n+3
namespace Index
private theorem upper_lt {lo hi : ℕ} (hl : lo ≤ hi) : ∀ p ∈ betaUpper hi lo, p.1 < p.2 := by { intro p hp; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp; have hh := List.mem_range.mp hj; dsimp; omega }
private theorem upper_nodup (lo hi : ℕ) : (betaUpper hi lo).Nodup := by { apply List.Nodup.map; · { intro i j he; have hh := congrArg Prod.fst he; dsimp at hh; omega }; · { exact List.nodup_range } }
private theorem indices_nodup {lo hi : ℕ} (hl : lo ≤ hi) : (indexList (betaUpper hi lo)).Nodup := by {
  rw [indexList,List.nodup_append']; refine ⟨upper_nodup _ _,?_,?_⟩;
  · { exact List.Nodup.map Prod.swap_injective (List.nodup_reverse.mpr (upper_nodup lo hi)) };
  · { rw [List.disjoint_left]; intro p hp hq; obtain ⟨q,hq',he⟩ := List.mem_map.mp hq; have hh := upper_lt hl _ (List.mem_reverse.mp hq'); rw [←he] at hp; have hh' := upper_lt hl _ hp; dsimp at hh'; omega } }
private theorem indices_get_upper (lo hi j : ℕ) (hj : j < (hi-lo+1)/2) : (indexList (betaUpper hi lo))[j]'(by { simp [indexList,betaUpper]; omega }) = (lo+j,hi-j) := by { simp only [indexList]; rw [List.getElem_append_left (by { simpa [betaUpper] using hj })]; simp [betaUpper] }
private theorem indices_get_lower (lo hi j : ℕ) (hj : (hi-lo+1)/2 ≤ j) (hj' : j < 2*((hi-lo+1)/2)) : (indexList (betaUpper hi lo))[j]'(by { simp [indexList,betaUpper]; omega }) = (hi-(2*((hi-lo+1)/2)-1-j),lo+(2*((hi-lo+1)/2)-1-j)) := by {
  simp only [indexList]; rw [List.getElem_append_right (by { simpa [betaUpper] using hj })];
  simp only [List.length_map,List.length_range,List.getElem_map,List.getElem_reverse];
  simp only [betaUpper, List.length_map, List.length_range, List.getElem_map, List.getElem_range];
  have he : (hi-lo+1)/2-1-(j-(hi-lo+1)/2) = 2*((hi-lo+1)/2)-1-j := by { omega }; rw [he]; rfl }
private theorem indices_mem {lo hi i j : ℕ} (hl : lo ≤ hi) : (i,j) ∈ indexList (betaUpper hi lo) ↔ lo ≤ i ∧ lo ≤ j ∧ i ≤ hi ∧ j ≤ hi ∧ i ≠ j ∧ i+j=lo+hi := by {
  constructor;
  · {
    intro hp; simp only [indexList,betaUpper,List.mem_append,List.mem_map,List.mem_reverse] at hp; rcases hp with ⟨t,ht,heq⟩ | ⟨p,⟨t,ht,heq⟩,hswap⟩;
    · { have ht' := List.mem_range.mp ht; cases heq; dsimp; omega }; · { cases heq; cases hswap; have ht' := List.mem_range.mp ht; dsimp; omega } };
  · {
    rintro ⟨hli,hlj,hih,hjh,hne,hsum⟩; by_cases hij : i<j;
    · { apply List.mem_append_left; apply List.mem_map.mpr; refine ⟨i-lo,List.mem_range.mpr (by { omega }),?_⟩; congr 1 <;> omega };
    · { apply List.mem_append_right; apply List.mem_map.mpr; refine ⟨(j,i),List.mem_reverse.mpr ?_,rfl⟩; apply List.mem_map.mpr; refine ⟨j-lo,List.mem_range.mpr (by { omega }),?_⟩; congr 1 <;> omega } } }
private theorem indices_length (lo hi : ℕ) : (indexList (betaUpper hi lo)).length=2*((hi-lo+1)/2) := by { simp [indexList,betaUpper]; omega }
private theorem indices_idxOf_upper {lo hi t : ℕ} (hl : lo ≤ hi) (ht : t < (hi-lo+1)/2) : (indexList (betaUpper hi lo)).idxOf (lo+t,hi-t)=t := by { rw [←indices_get_upper lo hi t ht]; exact (indices_nodup hl).idxOf_getElem _ _ }
private theorem indices_idxOf_lower {lo hi t : ℕ} (hl : lo ≤ hi) (ht : (hi-lo+1)/2 ≤ t) (ht' : t < 2*((hi-lo+1)/2)) : (indexList (betaUpper hi lo)).idxOf (hi-(2*((hi-lo+1)/2)-1-t),lo+(2*((hi-lo+1)/2)-1-t))=t := by { rw [←indices_get_lower lo hi t ht ht']; exact (indices_nodup hl).idxOf_getElem _ _ }
end Index
namespace Partition
open Index
def lo (n t : ℕ) := if t+2 ≤ n then 1 else t+3-n
def hi (n t : ℕ) := if t+2 ≤ n then t+2 else n
private def addresses (n t : ℕ) := indexList (betaUpper (hi n t) (lo n t))
private theorem bounds {n t : ℕ} (hn : 3 ≤ n) (ht : t < 2*n-3) : 1 ≤ lo n t ∧ lo n t < hi n t ∧ hi n t ≤ n ∧ lo n t+hi n t=t+3 := by { dsimp [lo,hi]; split_ifs <;> omega }
private theorem address_bounds {n t : ℕ} (hn : 3 ≤ n) (ht : t < 2*n-3) : ∀ p ∈ addresses n t, 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ≤ n ∧ p.2 ≤ n ∧ p.1 ≠ p.2 ∧ p.1+p.2=t+3 := by { intro p hp; have hb := bounds hn ht; have hh := (indices_mem (show lo n t ≤ hi n t by { omega })).mp hp; omega }
private def cycleAddress (n : ℕ) (hn : 3 ≤ n) (t : Fin (2*n-3)) (j : Fin (addresses n t.val).length) : (Fin n × Fin n) := let p := (addresses n t.val)[j.val]; have hp := address_bounds hn t.isLt p (List.getElem_mem j.isLt); (⟨p.1-1,by { omega }⟩,⟨p.2-1,by { omega }⟩)
private theorem cycleAddress_values {n : ℕ} (hn : 3 ≤ n) (t : Fin (2*n-3)) (j : Fin (addresses n t.val).length) : ((cycleAddress n hn t j).1.val+1,(cycleAddress n hn t j).2.val+1) = (addresses n t.val)[j.val] := by { have hp := address_bounds hn t.isLt _ (List.getElem_mem j.isLt); dsimp [cycleAddress]; apply Prod.ext <;> dsimp <;> omega }
private theorem cycleAddress_sum {n : ℕ} (hn : 3 ≤ n) (t : Fin (2*n-3)) (j : Fin (addresses n t.val).length) : (cycleAddress n hn t j).1.val+(cycleAddress n hn t j).2.val+2=t.val+3 := by { have hp := (address_bounds hn t.isLt _ (List.getElem_mem j.isLt)).2.2.2.2.2; rw [←cycleAddress_values hn t j] at hp; dsimp at hp; omega }
private theorem cycleAddress_ne {n : ℕ} (hn : 3 ≤ n) (t : Fin (2*n-3)) (j : Fin (addresses n t.val).length) : (cycleAddress n hn t j).1 ≠ (cycleAddress n hn t j).2 := by { have hp := (address_bounds hn t.isLt _ (List.getElem_mem j.isLt)).2.2.2.2.1; rw [←cycleAddress_values hn t j] at hp; intro h; apply hp; simpa [h] }
private theorem cycleAddress_injective {n : ℕ} (hn : 3 ≤ n) (t : Fin (2*n-3)) : Function.Injective (cycleAddress n hn t) := by {
  intro i j hij;
  have hget : (addresses n t.val)[i.val] = (addresses n t.val)[j.val] := by { rw [←cycleAddress_values hn t i,←cycleAddress_values hn t j,hij] };
  have hnd := indices_nodup (show lo n t.val ≤ hi n t.val by { have := bounds hn t.isLt; omega }); apply Fin.ext; exact hnd.getElem_inj_iff.mp hget }
private def dim (n : ℕ) : Option (Fin (2*n-3)) → ℕ | none => n | some t => (addresses n t.val).length
private def Address (n : ℕ) (hn : 3 ≤ n) : (Σ t, Fin (dim n t)) → (Fin n × Fin n) | ⟨none,j⟩ => (j,j) | ⟨some t,j⟩ => cycleAddress n hn t j
private theorem Address_injective {n : ℕ} (hn : 3 ≤ n) : Function.Injective (Address n hn) := by {
  rintro ⟨a,i⟩ ⟨b,j⟩ he;
  cases a with | none => { cases b with | none => { have hh := congrArg Prod.fst he; dsimp [Address] at hh; subst j; rfl } | some b => { have hh := cycleAddress_ne hn b j; dsimp [Address] at he; rw [←he] at hh; exact (hh rfl).elim } } | some a => {
    cases b with | none => { have hh := cycleAddress_ne hn a i; dsimp [Address] at he; rw [he] at hh; exact (hh rfl).elim } | some b => { have hs := cycleAddress_sum hn a i; have hs' := cycleAddress_sum hn b j; dsimp [Address] at he; rw [he] at hs; have hab : a=b := Fin.ext (by { omega }); subst b; have hij := cycleAddress_injective hn a he; subst j; rfl } } }
private theorem Address_surjective {n : ℕ} (hn : 3 ≤ n) : Function.Surjective (Address n hn) := by {
  rintro ⟨i,j⟩; by_cases hij : i=j; · { subst j; exact ⟨⟨none,i⟩,rfl⟩ };
  · {
    have hi_lt := i.isLt; have hj_lt := j.isLt; have hvals : i.val ≠ j.val := fun h => hij (Fin.ext h); let t : Fin (2*n-3) := ⟨i.val+j.val-1,by { omega }⟩;
    have ht : t.val+3=i.val+j.val+2 := by { dsimp [t]; omega }; have hb := bounds hn t.isLt;
    have hm : (i.val+1,j.val+1) ∈ addresses n t.val := by { apply (indices_mem (show lo n t.val ≤ hi n t.val by { omega })).mpr; dsimp [lo,hi]; split_ifs <;> omega };
    obtain ⟨k,hk,hget⟩ := List.mem_iff_getElem.mp hm; refine ⟨⟨some t,⟨k,hk⟩⟩,?_⟩; change cycleAddress n hn t ⟨k,hk⟩=(i,j);
    have hv := cycleAddress_values hn t ⟨k,hk⟩; rw [hget] at hv; apply Prod.ext <;> apply Fin.ext;
    · { change (cycleAddress n hn t ⟨k,hk⟩).1.val=i.val; have hh := congrArg Prod.fst hv; change (cycleAddress n hn t ⟨k,hk⟩).1.val+1=i.val+1 at hh; omega };
    · { change (cycleAddress n hn t ⟨k,hk⟩).2.val=j.val; have hh := congrArg Prod.snd hv; change (cycleAddress n hn t ⟨k,hk⟩).2.val+1=j.val+1 at hh; omega } } }
private def addressEquiv (n : ℕ) (hn : 3 ≤ n) : (Σ t, Fin (dim n t)) ≃ (Fin n × Fin n) := Equiv.ofBijective (Address n hn) ⟨Address_injective hn,Address_surjective hn⟩
end Partition
private theorem indexList_sum {upper : List (ℕ × ℕ)} {s : ℕ} (hupper : ∀ p ∈ upper, p.1+p.2=s) : ∀ p ∈ indexList upper, p.1+p.2=s := by { intro p hp; simp only [indexList,List.mem_append,List.mem_map,List.mem_reverse] at hp; rcases hp with hp | ⟨q,hq,rfl⟩; · { exact hupper p hp }; · { simpa [Nat.add_comm] using hupper q hq } }
private theorem blockEntry_antidiagonal {n : ℕ} (a : Fin n → ℂ) (upper : List (ℕ × ℕ)) (scale : ℂ) {s : ℕ} (hu : ∀ p ∈ upper, p.1+p.2=s) (row col : (Fin n × Fin n)) (h : row.1.val+row.2.val ≠ col.1.val+col.2.val) : blockEntry a upper scale row col = 0 := by { dsimp [blockEntry]; split_ifs with hh; · { have hr := indexList_sum hu _ hh.1; have hc := indexList_sum hu _ hh.2; exfalso; apply h; omega }; · { rfl } }
private theorem alphaUpper_sum (k : ℕ) : ∀ p ∈ alphaUpper k, p.1+p.2=k+1 := by { intro p hp; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp; have hjlt := List.mem_range.mp hj; dsimp; omega }
private theorem betaUpper_sum {n l : ℕ} (hl : l ≤ n) : ∀ p ∈ betaUpper n l, p.1+p.2=n+l := by { intro p hp; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp; have hjlt := List.mem_range.mp hj; dsimp; omega }
private theorem rhoGamma_antidiagonal {n : ℕ} (a b : Fin n → ℂ) (r : ℝ) (row col : (Fin n × Fin n)) (h : row.1.val+row.2.val ≠ col.1.val+col.2.val) : rhoGamma a b r row col=0 := by {
  have hs (a : Fin n → ℂ) (i j : ℕ) (z : ℂ) : blockEntry a [(i,j)] z row col=0 := blockEntry_antidiagonal a [(i,j)] z (s := i+j) (by { simp }) row col h;
  have ha : (∑ k ∈ Finset.range (n+1), if 4 ≤ k then blockEntry a (alphaUpper k) 1 row col else 0)=0 := by { apply Finset.sum_eq_zero; intro k hk; split_ifs; · { exact blockEntry_antidiagonal _ _ _ (alphaUpper_sum k) _ _ h }; · { rfl } };
  have hb : (∑ l ∈ Finset.range (n+1), if 2 ≤ l ∧ l+3 ≤ n then blockEntry b (betaUpper n l) 1 row col else 0)=0 := by { apply Finset.sum_eq_zero; intro l hl; split_ifs with hh; · { exact blockEntry_antidiagonal _ _ _ (betaUpper_sum (by { omega })) _ _ h }; · { rfl } };
  have hne : row ≠ col := by { intro he; exact h (he ▸ rfl) }; simp [rhoGamma,ha,hb,hs,hne] }
private theorem rho_diagonal_cross_zero {n : ℕ} (a b : Fin n → ℂ) (r : ℝ) (i j k : Fin n) (hjk : j ≠ k) : rho a b r (i,i) (j,k)=0 := by { apply rhoGamma_antidiagonal; intro he; dsimp at he; apply hjk; apply Fin.ext; omega }
namespace Partition
open Index
private theorem alphaUpper_eq_upper {k : ℕ} (hk : 1 ≤ k) : alphaUpper k=betaUpper k 1 := by { simp [alphaUpper,betaUpper,Nat.sub_add_cancel hk,Nat.add_comm] }
private theorem upper_single {lo hi : ℕ} (h1 : lo<hi) (h2 : hi≤lo+2) : betaUpper hi lo=[(lo,hi)] := by { have hm : (hi-lo+1)/2=1 := by { omega }; simp [betaUpper,hm] }
private theorem blockEntry_row_sum {n : ℕ} (a : Fin n → ℂ) (u : List (ℕ×ℕ)) (c : ℂ) {s : ℕ} (hu : ∀ p∈u, p.1+p.2=s) (row col : (Fin n × Fin n)) (hne : row.1.val+row.2.val+2≠s) : blockEntry a u c row col=0 := by { dsimp [blockEntry]; split_ifs with h; · { have hh := indexList_sum hu _ h.1; exfalso; apply hne; omega }; · { rfl } }
private theorem blockEntry_on_addresses {n : ℕ} (hn : 3 ≤ n) (a : Fin n → ℂ) (t : Fin (2*n-3)) (c : ℂ) (i j : Fin (addresses n t.val).length) : blockEntry a (betaUpper (hi n t.val) (lo n t.val)) c (cycleAddress n hn t i) (cycleAddress n hn t j) = c * P (addresses n t.val).length (blockZ a (betaUpper (hi n t.val) (lo n t.val))) i j := by {
  have hnd : (addresses n t.val).Nodup := indices_nodup (by { have := bounds hn t.isLt; omega }); dsimp only [blockEntry];
  change (if ((cycleAddress n hn t i).1.val+1,(cycleAddress n hn t i).2.val+1) ∈ addresses n t.val ∧ ((cycleAddress n hn t j).1.val+1,(cycleAddress n hn t j).2.val+1) ∈ addresses n t.val then c*pEntry (addresses n t.val).length _ ((addresses n t.val).idxOf _) ((addresses n t.val).idxOf _) else 0)=_;
  rw [cycleAddress_values,cycleAddress_values]; simp only [List.getElem_mem,and_self,if_true,hnd.idxOf_getElem]; rfl }
private def cycleScale (n t : ℕ) : ℂ := if t=1 ∨ t+5=2*n then 2 else 1
private def cyclePhase {n : ℕ} (a b : Fin n → ℂ) (t : ℕ) := if t+2≤n then a else b
private def CycleBlock {n : ℕ} (a b : Fin n → ℂ) (t : Fin (2*n-3)) : Matrix (Fin (addresses n t.val).length) (Fin (addresses n t.val).length) ℂ := cycleScale n t.val • P (addresses n t.val).length (blockZ (cyclePhase a b t.val) (betaUpper (hi n t.val) (lo n t.val)))
private theorem rhoGamma_on_cycle {n : ℕ} (hn : 3 ≤ n) (a b : Fin n → ℂ) (r : ℝ) (t : Fin (2*n-3)) (i j : Fin (addresses n t.val).length) : rhoGamma a b r (cycleAddress n hn t i) (cycleAddress n hn t j) = CycleBlock a b t i j := by {
  let row := cycleAddress n hn t i; let col := cycleAddress n hn t j; have hs : row.1.val+row.2.val+2=t.val+3 := cycleAddress_sum hn t i;
  have hne : row.1 ≠ row.2 := cycleAddress_ne hn t i;
  have hz (a : Fin n → ℂ) (p q : ℕ) (c : ℂ) (h : t.val+3≠p+q) : blockEntry a [(p,q)] c row col=0 := blockEntry_row_sum _ _ _ (s := p+q) (by { simp }) _ _ (by { omega });
  have haS (k : ℕ) (h : t.val+2≠k) : blockEntry a (alphaUpper k) 1 row col=0 := blockEntry_row_sum _ _ _ (alphaUpper_sum k) _ _ (by { omega });
  have hbS (l : ℕ) (hl : l≤n) (h : t.val+3≠n+l) : blockEntry b (betaUpper n l) 1 row col=0 := blockEntry_row_sum _ _ _ (betaUpper_sum hl) _ _ (by { omega });
  have hAsum : (∑ k∈Finset.range (n+1),if 4≤k then blockEntry a (alphaUpper k) 1 row col else 0) = if 4≤t.val+2 ∧ t.val+2≤n then blockEntry a (alphaUpper (t.val+2)) 1 row col else 0 := by {
    by_cases hkn : t.val+2≤n;
    · { rw [Finset.sum_eq_single_of_mem (t.val+2) (Finset.mem_range.mpr (by { omega }))]; · { simp [hkn] }; · { intro k hk hneq; split_ifs; · { exact haS k (Ne.symm hneq) }; · { rfl } } };
    · { rw [if_neg (by { omega })]; apply Finset.sum_eq_zero; intro k hk; have hk' := Finset.mem_range.mp hk; split_ifs; · { exact haS k (by { omega }) }; · { rfl } } };
  have hb := bounds hn t.isLt; by_cases hreg : t.val+2≤n;
  · {
    have hBsum : (∑ l∈Finset.range (n+1),if 2≤l ∧ l+3≤n then blockEntry b (betaUpper n l) 1 row col else 0)=0 := by { apply Finset.sum_eq_zero; intro l hl; split_ifs with hh; · { exact hbS l (by { omega }) (by { omega }) }; · { rfl } };
    have hnear : (if 3<n then blockEntry b [(n-2,n)] 2 row col else 0)=0 := by { split_ifs with hN; · { exact hz b (n-2) n 2 (by { omega }) }; · { rfl } };
    have hlast := hz b (n-1) n 1 (by { omega });
    have hu : betaUpper (hi n t.val) (lo n t.val)=alphaUpper (t.val+2) := by { simp only [lo,hi,if_pos hreg]; exact (alphaUpper_eq_upper (by { omega })).symm };
    have htarget := blockEntry_on_addresses hn a t (cycleScale n t.val) i j; dsimp [CycleBlock,cyclePhase];
    simp only [if_pos hreg,Matrix.smul_apply,smul_eq_mul]; rw [←htarget]; change rhoGamma a b r row col=_;
    simp only [rhoGamma,hne,false_and,if_false,zero_add,hAsum,hBsum,hnear,hlast,add_zero]; by_cases ht0 : t.val=0;
    · { have hu' : betaUpper (hi n t.val) (lo n t.val)=[(1,2)] := by { rw [hu,ht0]; norm_num [alphaUpper,List.range_succ] }; rw [hz a 1 3 2 (by { omega }),hu']; simp [ht0,cycleScale,show 5≠2*n by { omega },row,col] };
    · {
      by_cases ht1 : t.val=1;
      · { have hu' : betaUpper (hi n t.val) (lo n t.val)=[(1,3)] := by { rw [hu,ht1]; norm_num [alphaUpper,List.range_succ] }; rw [hz a 1 2 1 (by { omega })]; rw [hu']; simp [ht1,cycleScale,row,col] };
      · { rw [hz a 1 2 1 (by { omega }),hz a 1 3 2 (by { omega })]; simp [show 4≤t.val+2 by { omega },hreg,cycleScale,ht1,show t.val+5≠2*n by { omega },hu,row,col] } } };
  · {
    let l := t.val+3-n; have hl : 2≤l ∧ l≤n-1 ∧ n+l=t.val+3 := by { dsimp [l]; omega };
    have hBsum : (∑ q∈Finset.range (n+1),if 2≤q ∧ q+3≤n then blockEntry b (betaUpper n q) 1 row col else 0)= if l+3≤n then blockEntry b (betaUpper n l) 1 row col else 0 := by { rw [Finset.sum_eq_single_of_mem l (Finset.mem_range.mpr (by { omega }))]; · { simp [hl.1] }; · { intro q hq hneq; split_ifs with hh; · { exact hbS q (by { omega }) (by { omega }) }; · { rfl } } };
    have hu : betaUpper (hi n t.val) (lo n t.val)=betaUpper n l := by { simp only [lo,hi,if_neg hreg]; rfl };
    have htarget := blockEntry_on_addresses hn b t (cycleScale n t.val) i j; dsimp [CycleBlock,cyclePhase];
    simp only [if_neg hreg,Matrix.smul_apply,smul_eq_mul]; rw [←htarget]; change rhoGamma a b r row col=_;
    simp only [rhoGamma,hne,false_and,if_false,zero_add,hAsum,hBsum]; rw [hz a 1 2 1 (by { omega }),hz a 1 3 2 (by { omega })];
    simp only [zero_add,if_neg (show ¬(4≤t.val+2 ∧ t.val+2≤n) by { omega }),zero_add]; by_cases hlast : l=n-1;
    · {
      have hu' : betaUpper (hi n t.val) (lo n t.val)=[(n-1,n)] := by { rw [hu,hlast]; exact upper_single (by { omega }) (by { omega }) };
      have hnear : (if 3<n then blockEntry b [(n-2,n)] 2 row col else 0)=0 := by { split_ifs; · { exact hz b (n-2) n 2 (by { omega }) }; · { rfl } };
      simp [hnear,show ¬l+3≤n by { omega },cycleScale,show t.val≠1 by { omega }, show t.val+5≠2*n by { omega },hu',row,col] };
    · {
      by_cases hnear : l=n-2;
      · { have hu' : betaUpper (hi n t.val) (lo n t.val)=[(n-2,n)] := by { rw [hu,hnear]; exact upper_single (by { omega }) (by { omega }) }; rw [hz b (n-1) n 1 (by { omega })]; simp [show 3<n by { omega },show ¬l+3≤n by { omega },cycleScale, show t.val+5=2*n by { omega },hu',row,col] };
      · {
        have hnz : (if 3<n then blockEntry b [(n-2,n)] 2 row col else 0)=0 := by { split_ifs; · { exact hz b (n-2) n 2 (by { omega }) }; · { rfl } };
        rw [hz b (n-1) n 1 (by { omega })];
        simp [hnz,show l+3≤n by { omega },cycleScale,show t.val≠1 by { omega }, show t.val+5≠2*n by { omega },hu,row,col] } } } }
end Partition
namespace Partition
open Index
private theorem blockEntry_diagonal_zero {n : ℕ} (a : Fin n → ℂ) (u : List (ℕ×ℕ)) (c : ℂ) (hu : ∀ p∈u,p.1≠p.2) (row col : (Fin n × Fin n)) (hdiag : row.1=row.2 ∨ col.1=col.2) : blockEntry a u c row col=0 := by {
  have hall : ∀ p∈indexList u,p.1≠p.2 := by { intro p hp; simp only [indexList,List.mem_append,List.mem_map,List.mem_reverse] at hp; rcases hp with hp | ⟨q,hq,rfl⟩; · { exact hu p hp }; · { exact Ne.symm (hu q hq) } };
  dsimp [blockEntry]; split_ifs with hh;
  · { exfalso; rcases hdiag with h | h; · { exact hall _ hh.1 (by { simpa [h] }) }; · { exact hall _ hh.2 (by { simpa [h] }) } }; · { rfl } }
private theorem rhoGamma_diagonal_entry {n : ℕ} (hn : 3≤n) (a b : Fin n → ℂ) (r : ℝ) (row col : (Fin n × Fin n)) (hdiag : row.1=row.2 ∨ col.1=col.2) : rhoGamma a b r row col = if row.1=row.2 ∧ row=col then (r : ℂ) else 0 := by {
  have hz (a : Fin n → ℂ) (u : List (ℕ×ℕ)) (c : ℂ) (hu : ∀p∈u,p.1≠p.2) : blockEntry a u c row col=0 := blockEntry_diagonal_zero a u c hu row col hdiag;
  have h1 := hz a [(1,2)] 1 (by { simp }); have h2 := hz a [(1,3)] 2 (by { simp });
  have h3 : (∑ k∈Finset.range (n+1),if 4≤k then blockEntry a (alphaUpper k) 1 row col else 0)=0 := by { apply Finset.sum_eq_zero; intro k hk; split_ifs with h4; · { apply hz; rw [alphaUpper_eq_upper (by { omega })]; intro p hp; exact ne_of_lt (upper_lt (by { omega }) p hp) }; · { rfl } };
  have h4 : (∑ l∈Finset.range (n+1),if 2≤l ∧ l+3≤n then blockEntry b (betaUpper n l) 1 row col else 0)=0 := by { apply Finset.sum_eq_zero; intro l hl; split_ifs with hl'; · { apply hz; intro p hp; exact ne_of_lt (upper_lt (by { omega }) p hp) }; · { rfl } };
  have h5 : (if 3<n then blockEntry b [(n-2,n)] 2 row col else 0)=0 := by { split_ifs; · { exact hz b _ _ (by { simp; omega }) }; · { rfl } };
  have h6 := hz b [(n-1,n)] 1 (by { simp; omega }); simp only [rhoGamma,h1,h2,h3,h4,h5,h6,add_zero] }
private def GammaBlock {n : ℕ} (a b : Fin n → ℂ) (r : ℝ) : ∀ t, Matrix (Fin (dim n t)) (Fin (dim n t)) ℂ | none => (r : ℂ) • 1 | some t => CycleBlock a b t
set_option backward.isDefEq.respectTransparency false in private theorem rhoGamma_reindex {n : ℕ} (hn : 3≤n) (a b : Fin n → ℂ) (r : ℝ) : (rhoGamma a b r).submatrix (addressEquiv n hn) (addressEquiv n hn) = Matrix.blockDiagonal' (GammaBlock a b r) := by {
  ext ⟨t,i⟩ ⟨u,j⟩;
  cases t with | none => {
    cases u with | none => {
      change rhoGamma a b r (i,i) (j,j)=(Matrix.blockDiagonal' (GammaBlock a b r)) ⟨none,i⟩ ⟨none,j⟩;
      rw [Matrix.blockDiagonal'_apply_eq,rhoGamma_diagonal_entry hn _ _ _ _ _ (Or.inl rfl)];
      have hp : (i,i)=(j,j) ↔ i=j := ⟨fun h=>congrArg Prod.fst h,fun h=>by { subst j; rfl }⟩;
      simp only [GammaBlock,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]; simp only [eq_self,true_and,hp] } | some u => {
      change rhoGamma a b r (i,i) (cycleAddress n hn u j)=_;
      rw [rhoGamma_diagonal_entry hn _ _ _ _ _ (Or.inl rfl), Matrix.blockDiagonal'_apply_ne _ _ _ (by { simp })];
      have hh : (i,i) ≠ cycleAddress n hn u j := by { intro h; have hnz := cycleAddress_ne hn u j; rw [←h] at hnz; exact hnz rfl };
      exact if_neg (fun h=>hh h.2) } } | some t => {
    cases u with | none => { change rhoGamma a b r (cycleAddress n hn t i) (j,j)=_; rw [rhoGamma_diagonal_entry hn _ _ _ _ _ (Or.inr rfl), Matrix.blockDiagonal'_apply_ne _ _ _ (by { simp })]; simp [cycleAddress_ne hn t i] } | some u => {
      change rhoGamma a b r (cycleAddress n hn t i) (cycleAddress n hn u j)=_; by_cases htu : t=u;
      · { subst u; rw [Matrix.blockDiagonal'_apply_eq]; change rhoGamma a b r (cycleAddress n hn t i) (cycleAddress n hn t j) = CycleBlock a b t i j; exact rhoGamma_on_cycle hn a b r t i j };
      · { rw [Matrix.blockDiagonal'_apply_ne _ _ _ (by { simpa using htu })]; apply rhoGamma_antidiagonal; have ht := cycleAddress_sum hn t i; have hu := cycleAddress_sum hn u j; intro he; exact htu (Fin.ext (by { omega })) } } } }
end Partition

open Matrix
open scoped ComplexConjugate ComplexOrder MatrixOrder
namespace Cycle
private theorem real_psd_complex {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : (A.map Complex.ofReal).PosSemidef := by {
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg; rw [hB];
  have he : (star B*B).map Complex.ofReal = (B.map Complex.ofReal)ᴴ * B.map Complex.ofReal := by { change (star B*B).map Complex.ofRealHom = (B.map Complex.ofRealHom)ᴴ * B.map Complex.ofRealHom; rw [Matrix.map_mul]; congr 1; ext i j; simp [Matrix.conjTranspose_apply] };
  rw [he]; exact Matrix.posSemidef_conjTranspose_mul_self _ }
private theorem lap_complex_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj] : (G.lapMatrix ℝ).map Complex.ofReal = G.lapMatrix ℂ := by { ext i j; simp only [Matrix.map_apply,SimpleGraph.lapMatrix,Matrix.sub_apply,SimpleGraph.degMatrix, Matrix.diagonal_apply,SimpleGraph.adjMatrix_apply]; split_ifs <;> norm_num }
private theorem lap_complex_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj] : (G.lapMatrix ℂ).PosSemidef := by { rw [←lap_complex_eq]; exact real_psd_complex (G.posSemidef_lapMatrix ℝ) }
private theorem map_mulVec_re {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℂ) (i : ι) : ((A.map Complex.ofReal).mulVec x i).re = A.mulVec (fun j => (x j).re) i := by { simp [Matrix.mulVec,dotProduct,Complex.mul_re] }
private theorem map_mulVec_im {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℂ) (i : ι) : ((A.map Complex.ofReal).mulVec x i).im = A.mulVec (fun j => (x j).im) i := by { simp [Matrix.mulVec,dotProduct,Complex.mul_im] }
private theorem lap_complex_kernel {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj] (hc : G.Preconnected) (x : ι → ℂ) : (G.lapMatrix ℂ).mulVec x=0 ↔ ∀ i j, x i=x j := by {
  rw [←lap_complex_eq];
  have hr : ((G.lapMatrix ℝ).map Complex.ofReal).mulVec x=0 ↔ (G.lapMatrix ℝ).mulVec (fun j => (x j).re)=0 ∧ (G.lapMatrix ℝ).mulVec (fun j => (x j).im)=0 := by {
    constructor;
    · { intro h; constructor <;> funext i; · { simpa [map_mulVec_re] using congrArg Complex.re (congrFun h i) }; · { simpa [map_mulVec_im] using congrArg Complex.im (congrFun h i) } };
    · { rintro ⟨hr,hi⟩; funext i; apply Complex.ext; · { simpa [map_mulVec_re] using congrFun hr i }; · { simpa [map_mulVec_im] using congrFun hi i } } };
  rw [hr,G.lapMatrix_mulVec_eq_zero_iff_forall_reachable, G.lapMatrix_mulVec_eq_zero_iff_forall_reachable]; constructor;
  · { rintro ⟨hr,hi⟩ i j; exact Complex.ext (hr i j (hc i j)) (hi i j (hc i j)) };
  · { intro h; exact ⟨fun i j _ => congrArg Complex.re (h i j), fun i j _ => congrArg Complex.im (h i j)⟩ } }
private theorem hermitian_range {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) : v ∈ LinearMap.range A.mulVecLin ↔ ∀ x : ι → ℂ, A.mulVec x=0 → ∑ i, conj (x i)*v i=0 := by {
  let T := A.toEuclideanLin; have ht : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA;
  have he : T.range = T.kerᗮ := by { rw [←ht.orthogonal_range,Submodule.orthogonal_orthogonal] };
  have hm : v ∈ LinearMap.range A.mulVecLin ↔ (WithLp.toLp 2 v : EuclideanSpace ℂ ι) ∈ T.range := by {
    constructor; · { rintro ⟨x,hx⟩; refine ⟨WithLp.toLp 2 x,?_⟩; simpa [T,Matrix.toEuclideanLin_apply_piLp_toLp] using congrArg (WithLp.toLp 2) hx };
    · { rintro ⟨x,hx⟩; refine ⟨WithLp.ofLp x,?_⟩; simpa [T,Matrix.toEuclideanLin_apply,Matrix.mulVecLin_apply] using congrArg WithLp.ofLp hx } };
  rw [hm,he,Submodule.mem_orthogonal]; constructor;
  · { intro h x hx; have hh := h (WithLp.toLp 2 x) (by { change T (WithLp.toLp 2 x)=0; simpa [T,Matrix.toEuclideanLin_apply_piLp_toLp] using congrArg (WithLp.toLp 2) hx }); simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm] using hh };
  · { intro h x hx; have hh := h (WithLp.ofLp x) (by { change T x=0 at hx; simpa [T,Matrix.toEuclideanLin_apply] using congrArg WithLp.ofLp hx }); simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm] using hh } }
private theorem lap_complex_range {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : SimpleGraph ι) [DecidableRel G.Adj] (hc : G.Preconnected) (v : ι → ℂ) : v ∈ LinearMap.range (G.lapMatrix ℂ).mulVecLin ↔ ∑ i, v i=0 := by {
  rw [hermitian_range (lap_complex_psd G).isHermitian]; constructor; · { intro h; simpa using h (fun _=>1) (G.lapMatrix_mulVec_const_eq_zero) };
  · { intro h x hx; let i₀ := Classical.choice (inferInstance : Nonempty ι); have he : ∀ i, x i=x i₀ := fun i => (lap_complex_kernel G hc x).mp hx i i₀; simp_rw [he]; rw [←Finset.mul_sum,h,mul_zero] } }
end Cycle
namespace Cycle
private theorem cycle_adj_nat {d : ℕ} (hd : 2 ≤ d) (i j : Fin d) : (SimpleGraph.cycleGraph d).Adj i j ↔ j.val=i.val+1 ∨ i.val=j.val+1 ∨ (i.val=0 ∧ j.val+1=d) ∨ (j.val=0 ∧ i.val+1=d) := by {
  letI : NeZero d := ⟨by { omega }⟩; rw [SimpleGraph.cycleGraph_adj']; by_cases hij : i ≤ j;
  · {
    by_cases heq : i=j; · { subst j; simp only [sub_self,Fin.val_zero] at *; have hi := i.isLt; omega };
    · { have hlt : i < j := lt_of_le_of_ne hij heq; rw [Fin.sub_val_of_le hij,Fin.coe_sub_iff_lt.mpr hlt]; have hi := i.isLt; have hj := j.isLt; change i.val < j.val at hlt; omega } };
  · { have hlt : j < i := lt_of_not_ge hij; rw [Fin.sub_val_of_le hlt.le,Fin.coe_sub_iff_lt.mpr hlt]; have hi := i.isLt; have hj := j.isLt; change j.val < i.val at hlt; omega } }
private theorem cycle_degree {d : ℕ} (hd : 2 ≤ d) (i : Fin d) : (SimpleGraph.cycleGraph d).degree i = if d=2 then 1 else 2 := by { by_cases he : d=2; · { subst d; fin_cases i <;> decide }; · { obtain ⟨k,rfl⟩ : ∃ k, d=k+3 := ⟨d-3,by { omega }⟩; exact (SimpleGraph.cycleGraph_degree_three_le (v := i)) } }
private theorem cycle_lap_entry {d : ℕ} (hd : 2 ≤ d) (i j : Fin d) : (SimpleGraph.cycleGraph d).lapMatrix ℂ i j = if i=j then (if d=2 then 1 else 2) else if (SimpleGraph.cycleGraph d).Adj i j then -1 else 0 := by { simp only [SimpleGraph.lapMatrix,Matrix.sub_apply,SimpleGraph.degMatrix, Matrix.diagonal_apply,SimpleGraph.adjMatrix_apply]; by_cases he : i=j; · { subst j; simp [cycle_degree hd] }; · { simp only [if_neg he,zero_sub]; split_ifs <;> simp } }
private theorem sign_square (i : ℕ) : (-1 : ℂ)^i * (-1 : ℂ)^i=1 := by { rw [←pow_add,show i+i=2*i by { omega },pow_mul]; norm_num }
private theorem sign_adj {i j : ℕ} (h : j=i+1) : (-1 : ℂ)^i * (-1 : ℂ)^j = -1 := by { rw [h,pow_succ,←mul_assoc,sign_square,one_mul] }
private theorem sign_last {d : ℕ} (hd : 2 ≤ d) (he : Even d) : (-1 : ℂ)^(d-1) = -1 := by { obtain ⟨k,hk⟩ := he; have hh : d-1=2*(k-1)+1 := by { omega }; rw [hh,pow_succ,pow_mul]; norm_num }
private theorem pEntry_cycle {d : ℕ} (hd : 2 ≤ d) {z : ℕ → ℂ} (hz : z 0=1) (i j : Fin d) : P d z i j = if i=j then (if d=2 then 1 else 2) else if (SimpleGraph.cycleGraph d).Adj i j then z j.val/z i.val else 0 := by { change pEntry d z i.val j.val = _; simp only [cycle_adj_nat hd]; dsimp [pEntry]; have he : i.val=j.val ↔ i=j := Fin.ext_iff.symm; simp only [he]; split_ifs <;> simp_all [div_eq_mul_inv] <;> try { omega }; all_goals { first | { simp_all [hz] } | { ring } } }
private def gauge {d : ℕ} (z : ℕ → ℂ) (i : Fin d) : ℂ := (-1)^i.val*z i.val
private theorem P_gauge {d : ℕ} (hd : 2 ≤ d) (he : Even d) {z : ℕ → ℂ} (hz : z 0=1) (hnz : ∀ i : Fin d, z i.val ≠ 0) : P d z = Matrix.diagonal (fun i : Fin d => (gauge z i)⁻¹) * (SimpleGraph.cycleGraph d).lapMatrix ℂ * Matrix.diagonal (gauge z) := by {
  ext i j; rw [pEntry_cycle hd hz,Matrix.mul_diagonal,Matrix.diagonal_mul,cycle_lap_entry hd];
  have hs (i : Fin d) : (-1 : ℂ)^i.val ≠ 0 := pow_ne_zero _ (by { norm_num }); have hii : i=j → gauge z i=gauge z j := fun h => congrArg (gauge z) h;
  by_cases hij : i=j; · { subst j; simp only [if_pos rfl]; dsimp [gauge]; split_ifs <;> field_simp [hs i,hnz i] <;> ring };
  · {
    simp only [if_neg hij]; by_cases ha : (SimpleGraph.cycleGraph d).Adj i j;
    · {
      simp only [if_pos ha];
      have hsign : (-1 : ℂ)^i.val * (-1 : ℂ)^j.val = -1 := by {
        rcases (cycle_adj_nat hd i j).mp ha with h | h | ⟨h0,hl⟩ | ⟨h0,hl⟩; · { exact sign_adj h }; · { simpa only [mul_comm] using sign_adj h };
        · { rw [h0,pow_zero,one_mul,show j.val=d-1 by { omega },sign_last hd he] };
        · { rw [h0,pow_zero,mul_one,show i.val=d-1 by { omega },sign_last hd he] } };
      dsimp [gauge]; field_simp [hs i,hs j,hnz i,hnz j];
      have hsum : (-1 : ℂ)^i.val + (-1 : ℂ)^j.val=0 := by { linear_combination (-1 : ℂ)^i.val*hsign - sign_square i.val*(-1 : ℂ)^j.val };
      linear_combination hsum };
    · { simp [ha] } } }
end Cycle
namespace Cycle
private theorem lap_complex_rank {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : SimpleGraph ι) [DecidableRel G.Adj] (hc : G.Preconnected) : (G.lapMatrix ℂ).rank = Fintype.card ι-1 := by {
  classical {
    have hk : LinearMap.ker (G.lapMatrix ℂ).mulVecLin = ℂ ∙ (fun _ : ι => (1 : ℂ)) := by { ext x; rw [LinearMap.mem_ker,Matrix.mulVecLin_apply,lap_complex_kernel G hc,Submodule.mem_span_singleton]; constructor; · { intro h; let i := Classical.choice (inferInstance : Nonempty ι); exact ⟨x i,funext fun j => by { simp [h j i] }⟩ }; · { rintro ⟨c,rfl⟩; simp } };
    have hnonzero : (fun _ : ι => (1 : ℂ)) ≠ 0 := by { intro he; have h := congrFun he (Classical.choice (inferInstance : Nonempty ι)); norm_num at h };
    have h := (G.lapMatrix ℂ).mulVecLin.finrank_range_add_finrank_ker; rw [hk,finrank_span_singleton hnonzero,Module.finrank_pi] at h;
    change (G.lapMatrix ℂ).rank+1=Fintype.card ι at h; omega } }
private theorem diagonal_similarity_range {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℂ) (g : ι → ℂ) (hg : ∀ i, g i ≠ 0) (v : ι → ℂ) : v ∈ LinearMap.range (Matrix.diagonal (fun i => (g i)⁻¹)*L*Matrix.diagonal g).mulVecLin ↔ (fun i => g i*v i) ∈ LinearMap.range L.mulVecLin := by {
  have hmul (x : ι → ℂ) : (Matrix.diagonal (fun i => (g i)⁻¹)*L*Matrix.diagonal g).mulVec x = fun i => (g i)⁻¹ * L.mulVec (fun j => g j*x j) i := by { rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]; funext i; rw [Matrix.mulVec_diagonal]; congr 2; funext j; rw [Matrix.mulVec_diagonal] };
  constructor;
  · {
    rintro ⟨x,hx⟩; refine ⟨fun j => g j*x j,?_⟩; change L.mulVec (fun j => g j*x j)=_;
    change (Matrix.diagonal (fun i => (g i)⁻¹)*L*Matrix.diagonal g).mulVec x=v at hx; rw [hmul] at hx; funext i; have h := congrFun hx i;
    exact (mul_inv_cancel_left₀ (hg i) _).symm.trans (congrArg (g i * ·) h) };
  · {
    rintro ⟨x,hx⟩; refine ⟨fun i => (g i)⁻¹*x i,?_⟩; change (Matrix.diagonal (fun i => (g i)⁻¹)*L*Matrix.diagonal g).mulVec _=_; rw [hmul];
    have he : (fun i => g i*((g i)⁻¹*x i))=x := by { funext i; simp [hg i] }; rw [he]; change L.mulVec x=(fun i => g i*v i) at hx; rw [hx]; funext i;
    simp [hg i] } }
private theorem P_range {d : ℕ} (hd : 2 ≤ d) (he : Even d) {z : ℕ → ℂ} (hz : z 0=1) (hnz : ∀ i : Fin d, z i.val ≠ 0) (v : Fin d → ℂ) : v ∈ LinearMap.range (P d z).mulVecLin ↔ ∑ i : Fin d, (-1 : ℂ)^i.val*z i.val*v i=0 := by { letI : Nonempty (Fin d) := ⟨⟨0,by { omega }⟩⟩; rw [P_gauge hd he hz hnz,diagonal_similarity_range]; · { exact lap_complex_range _ SimpleGraph.cycleGraph_preconnected _ }; · { intro i; exact mul_ne_zero (pow_ne_zero _ (by { norm_num })) (hnz i) } }
private theorem P_rank {d : ℕ} (hd : 2 ≤ d) (he : Even d) {z : ℕ → ℂ} (hz : z 0=1) (hnz : ∀ i : Fin d, z i.val ≠ 0) : (P d z).rank=d-1 := by {
  letI : Nonempty (Fin d) := ⟨⟨0,by { omega }⟩⟩; have hg : ∀ i : Fin d, gauge z i ≠ 0 := fun i => mul_ne_zero (pow_ne_zero _ (by { norm_num })) (hnz i);
  rw [P_gauge hd he hz hnz];
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by { rw [Matrix.det_diagonal]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (by { simp [hg] })) })];
  rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by { rw [Matrix.det_diagonal]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (by { simp [hg] })) })];
  simpa using lap_complex_rank (SimpleGraph.cycleGraph d) SimpleGraph.cycleGraph_preconnected }
private theorem P_psd {d : ℕ} (hd : 2 ≤ d) (he : Even d) {z : ℕ → ℂ} (hz : z 0=1) (hunit : ∀ i : Fin d, ‖z i.val‖=1) : (P d z).PosSemidef := by {
  have hnz : ∀ i : Fin d, z i.val ≠ 0 := fun i => norm_ne_zero_iff.mp (by { rw [hunit i]; norm_num });
  have hg : ∀ i : Fin d, ‖gauge z i‖=1 := by { intro i; simp [gauge,norm_mul,norm_pow,hunit] }; rw [P_gauge hd he hz hnz];
  have heq : Matrix.diagonal (fun i : Fin d => (gauge z i)⁻¹) = (Matrix.diagonal (gauge z))ᴴ := by { ext i j; by_cases hij : i=j; · { subst j; simp [Matrix.conjTranspose_apply,Matrix.diagonal_apply,Complex.inv_eq_conj (hg i)] }; · { simp [Matrix.conjTranspose_apply,Matrix.diagonal_apply,hij,Ne.symm hij] } };
  rw [heq]; exact (lap_complex_psd _).conjTranspose_mul_mul_same _ }
end Cycle

open Matrix
open scoped ComplexOrder MatrixOrder
namespace Blocks
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
private theorem mulVec_block (M : ∀ i, Matrix (κ i) (κ i) ℂ) (v : (Σ i,κ i) → ℂ) (i : ι) (j : κ i) : (Matrix.blockDiagonal' M).mulVec v ⟨i,j⟩ = (M i).mulVec (fun k => v ⟨i,k⟩) j := by { simp only [Matrix.mulVec,dotProduct,Fintype.sum_sigma]; rw [Finset.sum_eq_single i]; · { simp only [Matrix.blockDiagonal'_apply_eq] }; · { intro k hk hki; apply Finset.sum_eq_zero; intro l hl; rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hki),zero_mul] }; · { simp } }
private theorem range_block (M : ∀ i, Matrix (κ i) (κ i) ℂ) (v : (Σ i,κ i) → ℂ) : v ∈ LinearMap.range (Matrix.blockDiagonal' M).mulVecLin ↔ ∀ i, (fun k => v ⟨i,k⟩) ∈ LinearMap.range (M i).mulVecLin := by {
  constructor; · { rintro ⟨x,hx⟩ i; refine ⟨fun k=>x ⟨i,k⟩,?_⟩; funext j; simpa only [Matrix.mulVecLin_apply,mulVec_block] using congrFun hx ⟨i,j⟩ };
  · { intro h; choose x hx using h; refine ⟨fun ij => x ij.1 ij.2,?_⟩; funext ⟨i,j⟩; simpa only [Matrix.mulVecLin_apply,mulVec_block] using congrFun (hx i) j } }
private def kernelEquiv (M : ∀ i, Matrix (κ i) (κ i) ℂ) : LinearMap.ker (Matrix.blockDiagonal' M).mulVecLin ≃ₗ[ℂ] ∀ i, LinearMap.ker (M i).mulVecLin where toFun x i := ⟨fun j=>x.val ⟨i,j⟩,by { have hx := x.property; change (Matrix.blockDiagonal' M).mulVec x.val=0 at hx; change (M i).mulVec (fun j=>x.val ⟨i,j⟩)=0; funext j; simpa only [mulVec_block,Pi.zero_apply] using congrFun hx ⟨i,j⟩ }⟩; invFun y := ⟨fun ij=>(y ij.1).val ij.2,by { change (Matrix.blockDiagonal' M).mulVec _=0; funext ⟨i,j⟩; have hy := (y i).property; change (M i).mulVec (y i).val=0 at hy; simpa only [mulVec_block,Pi.zero_apply] using congrFun hy j }⟩; left_inv x := by { apply Subtype.ext; rfl }; right_inv y := by { funext i; apply Subtype.ext; rfl }; map_add' x y := rfl; map_smul' c x := rfl
private theorem rank_block (M : ∀ i, Matrix (κ i) (κ i) ℂ) : (Matrix.blockDiagonal' M).rank=∑ i,(M i).rank := by {
  have htot := (Matrix.blockDiagonal' M).mulVecLin.finrank_range_add_finrank_ker;
  have hker : Module.finrank ℂ (LinearMap.ker (Matrix.blockDiagonal' M).mulVecLin) = ∑ i, Module.finrank ℂ (LinearMap.ker (M i).mulVecLin) := (kernelEquiv M).finrank_eq.trans (Module.finrank_pi_fintype ℂ);
  rw [hker,Module.finrank_pi,Fintype.card_sigma] at htot; change (Matrix.blockDiagonal' M).rank+_= _ at htot;
  have hs : ∑ i, ((M i).rank+Module.finrank ℂ (LinearMap.ker (M i).mulVecLin)) = ∑ i,Fintype.card (κ i) := by { apply Finset.sum_congr rfl; intro i hi; simpa only [Matrix.rank,Module.finrank_pi] using (M i).mulVecLin.finrank_range_add_finrank_ker };
  rw [Finset.sum_add_distrib] at hs; omega }
private theorem psd_block (M : ∀ i, Matrix (κ i) (κ i) ℂ) (hM : ∀ i,(M i).PosSemidef) : (Matrix.blockDiagonal' M).PosSemidef := by {
  have h : ∀ i,∃ B : Matrix (κ i) (κ i) ℂ, M i=star B*B := fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM i).nonneg; choose B hB using h;
  have he : Matrix.blockDiagonal' M = (Matrix.blockDiagonal' B)ᴴ*Matrix.blockDiagonal' B := by { rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul]; congr 1; funext i; exact hB i };
  rw [he]; exact Matrix.posSemidef_conjTranspose_mul_self _ }
end Blocks
namespace Blocks
variable {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]
private theorem range_submatrix (A : Matrix ι ι ℂ) (e : ν ≃ ι) (v : ι → ℂ) : v ∈ LinearMap.range A.mulVecLin ↔ (v ∘ e) ∈ LinearMap.range (A.submatrix e e).mulVecLin := by {
  constructor;
  · { rintro ⟨x,hx⟩; refine ⟨x ∘ e,?_⟩; change (A.submatrix e e).mulVec (x ∘ e)=v ∘ e; rw [Matrix.submatrix_mulVec_equiv]; simpa only [Matrix.mulVecLin_apply,Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id] using congrArg (· ∘ e) hx };
  · { rintro ⟨x,hx⟩; refine ⟨x ∘ e.symm,?_⟩; change (A.submatrix e e).mulVec x=v ∘ e at hx; rw [Matrix.submatrix_mulVec_equiv] at hx; funext i; simpa using congrFun hx (e.symm i) } }
private theorem range_smul (A : Matrix ι ι ℂ) {c : ℂ} (hc : c≠0) (v : ι → ℂ) : v ∈ LinearMap.range (c • A).mulVecLin ↔ v ∈ LinearMap.range A.mulVecLin := by {
  constructor; · { rintro ⟨x,hx⟩; refine ⟨c • x,?_⟩; simpa only [Matrix.mulVecLin_apply,Matrix.smul_mulVec,Matrix.mulVec_smul] using hx };
  · { rintro ⟨x,hx⟩; refine ⟨c⁻¹ • x,?_⟩; simpa only [Matrix.mulVecLin_apply,Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul, mul_inv_cancel₀ hc,inv_mul_cancel₀ hc,one_smul] using hx } }
end Blocks
namespace Partition
open Index
private theorem cycle_length {n : ℕ} (hn : 3≤n) (t : Fin (2*n-3)) : 2≤(addresses n t.val).length ∧ Even (addresses n t.val).length := by { have hb := bounds hn t.isLt; rw [addresses,indices_length]; constructor; · { omega }; · { exact even_two_mul _ } }
private theorem blockZ_zero {lo hi n : ℕ} (h : lo<hi) (a : Fin n → ℂ) : blockZ a (betaUpper hi lo) 0=1 := by { have hm : 0<(hi-lo+1)/2 := by { omega }; simp [blockZ,betaUpper,hm] }
private theorem blockZ_unit {lo hi n : ℕ} (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖=1) (j : ℕ) : ‖blockZ a (betaUpper hi lo) j‖=1 := by { have hu (k : ℕ) : ‖phaseAt a k‖=1 := by { unfold phaseAt; split_ifs <;> simp [ha] }; unfold blockZ; split_ifs; · { simp }; · { split <;> simp [norm_mul,norm_inv,hu] } }
private theorem sign_reflect {m j : ℕ} (hj : j<m) : (-1 : ℂ)^(2*m-1-j) = -(-1 : ℂ)^j := by { have hh : 2*m-1-j+j=2*m-1 := by { omega }; have hp : (-1 : ℂ)^(2*m-1-j)*(-1 : ℂ)^j = -1 := by { rw [←pow_add,hh,Cycle.sign_last (by { omega }) (even_two_mul m)] }; linear_combination (-1 : ℂ)^j*hp - Cycle.sign_square j*(-1 : ℂ)^(2*m-1-j) }
private theorem cycle_tensor_value {n : ℕ} (hn : 3≤n) (t : Fin (2*n-3)) (x y : Fin n → ℂ) (j : Fin (addresses n t.val).length) : tensor x y (cycleAddress n hn t j) = phaseAt x ((addresses n t.val)[j.val]).1 * phaseAt y ((addresses n t.val)[j.val]).2 := by { have hp := address_bounds hn t.isLt _ (List.getElem_mem j.isLt); dsimp [tensor,Matrix.vecMulVec,phaseAt,cycleAddress]; simp only [dif_pos (show ((addresses n t.val)[j.val]).1-1<n by { omega }), dif_pos (show ((addresses n t.val)[j.val]).2-1<n by { omega })] }
private def cycleTerm {n : ℕ} (a x y : Fin n → ℂ) (lo hi j : ℕ) : ℂ := let p := ((indexList (betaUpper hi lo))[j]?).getD (0,0); (-1)^j * blockZ a (betaUpper hi lo) j * phaseAt x p.1 * phaseAt y p.2
private theorem cycleTerm_upper {n lo hi j : ℕ} (a x y : Fin n → ℂ) (hj : j<(hi-lo+1)/2) : cycleTerm a x y lo hi j = (-1)^j*phaseAt x (lo+j)*phaseAt y (hi-j) := by { have hget := indices_get_upper lo hi j hj; have hlen : j<(indexList (betaUpper hi lo)).length := by { rw [indices_length]; omega }; simp only [cycleTerm,List.getElem?_eq_getElem hlen,Option.getD_some,hget]; have hu : j<(betaUpper hi lo).length := by { simpa [betaUpper] using hj }; simp [blockZ,hu] }
private theorem cycleTerm_lower {n lo hi j : ℕ} (a x y : Fin n → ℂ) (hj : j<(hi-lo+1)/2) : cycleTerm a x y lo hi (2*((hi-lo+1)/2)-1-j) = -(-1)^j*((phaseAt a (lo+j))⁻¹*phaseAt a (hi-j))* phaseAt x (hi-j)*phaseAt y (lo+j) := by {
  let m := (hi-lo+1)/2; have hge : m≤2*m-1-j := by { omega }; have hlt : 2*m-1-j<2*m := by { omega };
  have hget := indices_get_lower lo hi (2*m-1-j) hge hlt; have href : 2*m-1-(2*m-1-j)=j := by { omega }; rw [href] at hget;
  have hlen : 2*m-1-j<(indexList (betaUpper hi lo)).length := by { rw [indices_length]; exact hlt };
  have hu : ¬2*m-1-j<(betaUpper hi lo).length := by { simpa [betaUpper] using (by { omega } : ¬2*m-1-j<m) }; dsimp only [m] at hget hlen hu;
  have hidx : (indexList (betaUpper hi lo))[2*((hi-lo+1)/2)-1-j]?=some (hi-j,lo+j) := by { rw [List.getElem?_eq_getElem hlen,hget] };
  have hidx' : (indexList (betaUpper hi lo))[2*((hi-lo+1)/2)-1-j]?=some (hi-j,lo+j) := hidx; simp only [cycleTerm,hidx,Option.getD_some,blockZ,if_neg hu,hidx'];
  rw [sign_reflect hj] }
private theorem cycleTerm_sum {n lo hi : ℕ} (a x y : Fin n → ℂ) : (∑ i : Fin (indexList (betaUpper hi lo)).length, cycleTerm a x y lo hi i.val) = ∑ j∈Finset.range ((hi-lo+1)/2),(-1 : ℂ)^j*bracket a x y (lo+j) (hi-j) := by {
  rw [Fin.sum_univ_eq_sum_range,indices_length,show 2*((hi-lo+1)/2)=(hi-lo+1)/2+(hi-lo+1)/2 by { omega }, Finset.sum_range_add];
  rw [←Finset.sum_range_reflect (fun j=>cycleTerm a x y lo hi ((hi-lo+1)/2+j))]; rw [←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j hj;
  have hj' := Finset.mem_range.mp hj; have he : (hi-lo+1)/2+((hi-lo+1)/2-1-j)=2*((hi-lo+1)/2)-1-j := by { omega };
  rw [he,cycleTerm_upper a x y hj',cycleTerm_lower a x y hj']; dsimp [bracket]; ring }
private theorem cycle_sum_brackets {n : ℕ} (hn : 3≤n) (t : Fin (2*n-3)) (a x y : Fin n → ℂ) : (∑ i : Fin (addresses n t.val).length,(-1 : ℂ)^i.val* blockZ a (betaUpper (hi n t.val) (lo n t.val)) i.val*tensor x y (cycleAddress n hn t i)) = ∑ j∈Finset.range ((hi n t.val-lo n t.val+1)/2), (-1 : ℂ)^j*bracket a x y (lo n t.val+j) (hi n t.val-j) := by { rw [←cycleTerm_sum]; apply Finset.sum_congr rfl; intro i hi; rw [cycle_tensor_value]; have he : indexList (betaUpper (Partition.hi n t.val) (lo n t.val))=addresses n t.val := rfl; simp only [cycleTerm,he,List.getElem?_eq_getElem i.isLt,Option.getD_some]; ring }
end Partition
namespace Partition
open Index
private theorem cycleBlock_range {n : ℕ} (hn : 3≤n) (a b x y : Fin n → ℂ) (ha : ∀ i, ‖a i‖=1) (hb : ∀ i, ‖b i‖=1) (t : Fin (2*n-3)) : (fun i => tensor x y (cycleAddress n hn t i)) ∈ LinearMap.range (CycleBlock a b t).mulVecLin ↔ ∑ j∈Finset.range ((hi n t.val-lo n t.val+1)/2),(-1 : ℂ)^j* bracket (cyclePhase a b t.val) x y (lo n t.val+j) (hi n t.val-j)=0 := by {
  have hbounds := bounds hn t.isLt; have hlen := cycle_length hn t; have hz := blockZ_zero (show lo n t.val<hi n t.val by { omega }) (cyclePhase a b t.val);
  have hu : ∀ i, ‖cyclePhase a b t.val i‖=1 := by { intro i; unfold cyclePhase; split_ifs <;> first | { exact ha i } | { exact hb i } };
  have hnz : ∀ i : Fin (addresses n t.val).length, blockZ (cyclePhase a b t.val) (betaUpper (hi n t.val) (lo n t.val)) i.val≠0 := by { intro i; exact norm_ne_zero_iff.mp (by { rw [blockZ_unit _ hu]; norm_num }) };
  rw [CycleBlock,Blocks.range_smul _ (by { unfold cycleScale; split_ifs <;> norm_num }), Cycle.P_range hlen.1 hlen.2 hz hnz,cycle_sum_brackets hn t] }
private def CycleEquations {n : ℕ} (a b x y : Fin n → ℂ) : Prop := ∀ t : Fin (2*n-3), ∑ j∈Finset.range ((hi n t.val-lo n t.val+1)/2),(-1 : ℂ)^j* bracket (cyclePhase a b t.val) x y (lo n t.val+j) (hi n t.val-j)=0
private theorem cycleEquations_iff {n : ℕ} (hn : 3≤n) (a b x y : Fin n → ℂ) : CycleEquations a b x y ↔ BilinearSystem a b x y := by {
  constructor;
  · {
    intro h; constructor;
    · {
      intro k hk; have hk' := Finset.mem_Icc.mp hk; let t : Fin (2*n-3) := ⟨k-2,by { omega }⟩; have hh := h t;
      have he : t.val+2=k := by { dsimp [t]; omega }; have hreg : t.val+2≤n := by { omega }; simp only [lo,hi,cyclePhase,if_pos hreg] at hh;
      simpa only [Nat.sub_add_cancel (by { omega } : 1≤t.val+2),Nat.sub_add_cancel (by { omega } : 1≤k),Nat.one_add,Nat.succ_eq_add_one,he] using hh };
    · {
      intro l hl; have hl' := Finset.mem_Icc.mp hl; let t : Fin (2*n-3) := ⟨2*n-l-3,by { omega }⟩; have hh := h t;
      have hreg : ¬t.val+2≤n := by { dsimp [t]; omega }; have hlo : t.val+3-n=n-l := by { dsimp [t]; omega }; have hcount : n-(n-l)+1=l+1 := by { omega };
      simpa only [lo,hi,cyclePhase,if_neg hreg,hlo,hcount] using hh } };
  · {
    rintro ⟨ha,hb⟩ t; by_cases hreg : t.val+2≤n;
    · { have hh := ha (t.val+2) (Finset.mem_Icc.mpr ⟨by { omega },hreg⟩); simpa only [lo,hi,cyclePhase,if_pos hreg,Nat.sub_add_cancel (by { omega } : 1≤t.val+2), Nat.one_add] using hh };
    · {
      let l := 2*n-t.val-3; have hl : l∈Finset.Icc 1 (n-2) := by { dsimp [l]; simp only [Finset.mem_Icc]; omega }; have hh := hb l hl;
      have hlo : t.val+3-n=n-l := by { dsimp [l]; omega }; have hcount : n-(n-l)+1=l+1 := by { dsimp [l]; omega };
      simpa only [lo,hi,cyclePhase,if_neg hreg,hlo,hcount] using hh } } }
private theorem rhoGamma_range_core {n : ℕ} (hn : 3≤n) (a b x y : Fin n → ℂ) (r : ℝ) (ha : ∀ i, ‖a i‖=1) (hb : ∀ i, ‖b i‖=1) (hr : r≠0) : InRange (rhoGamma a b r) (tensor x y) ↔ BilinearSystem a b x y := by {
  unfold InRange; rw [Blocks.range_submatrix _ (addressEquiv n hn),rhoGamma_reindex hn,Blocks.range_block]; rw [←cycleEquations_iff hn]; constructor;
  · { intro h t; exact (cycleBlock_range hn a b x y ha hb t).mp (h (some t)) };
  · { intro h t; cases t with | none => { apply (Blocks.range_smul _ (by { exact_mod_cast hr }) _).mpr; refine ⟨fun i=>tensor x y (i,i),?_⟩; simp only [Matrix.mulVecLin_apply,Matrix.one_mulVec]; rfl } | some t => { exact (cycleBlock_range hn a b x y ha hb t).mpr (h t) } } }
end Partition
private theorem range_reduction : range_reduction_statement := by { intro n hn a b x y r hab hr; exact Partition.rhoGamma_range_core hn a b (fun i=>conj (x i)) y r (fun i=>(hab.1 i).1) (fun i=>(hab.1 i).2) (by { linarith }) }
namespace Draft
private def wedge {ι : Type*} (u v : ι → ℂ) (i j : ι) := u i * v j - u j * v i
private theorem wedge_trans {ι : Type*} {u v : ι → ℂ} {p i j : ι} (hp : u p ≠ 0 ∨ v p ≠ 0) (hi : wedge u v p i = 0) (hj : wedge u v p j = 0) : wedge u v i j = 0 := by {
  rcases hp with hp | hp;
  · { apply (mul_eq_zero.mp (show u p * wedge u v i j = 0 by { dsimp [wedge] at *; linear_combination u i * hj - u j * hi })).resolve_left hp };
  · { apply (mul_eq_zero.mp (show v p * wedge u v i j = 0 by { dsimp [wedge] at *; linear_combination v i * hj - v j * hi })).resolve_left hp } }
/-- A weighted alternating antidiagonal system propagates to every triangular minor. -/
theorem triangular_pivot {u v : ℕ → ℂ} {weight : ℕ → ℕ → ℂ} {N p : ℕ} (hp : 1 ≤ p) (hpactive : u p ≠ 0 ∨ v p ≠ 0) (hbefore : ∀ i, 1 ≤ i → i < p → u i = 0 ∧ v i = 0) (hw : ∀ k i, 2 ≤ k → k ≤ N → i < k / 2 → weight k i ≠ 0) (hsys : ∀ k, 2 ≤ k → k ≤ N → ∑ j ∈ Finset.range (k / 2), weight k j * wedge u v (j+1) (k-j) = 0) : ∀ q, p < q → p + q ≤ N+1 → wedge u v p q = 0 := by {
  intro q;
  induction q using Nat.strong_induction_on with | h q ih => {
    intro hpq hsum; let k := p + q - 1; have hk : 2 ≤ k ∧ k ≤ N := by { dsimp [k]; omega };
    have hpterm : p-1 ∈ Finset.range (k/2) := by { simp only [Finset.mem_range]; dsimp [k]; omega };
    have hother : ∀ j ∈ Finset.range (k/2), j ≠ p-1 → weight k j * wedge u v (j+1) (k-j) = 0 := by {
      intro j hj hne; have hjlt : j < k/2 := Finset.mem_range.mp hj; by_cases hsmall : j+1 < p;
      · { obtain ⟨hu,hv⟩ := hbefore (j+1) (by { omega }) hsmall; simp [wedge, hu, hv] };
      · {
        have hpi : p < j+1 := by { omega }; have hpj : p < k-j := by { dsimp [k] at *; omega }; have hiq : j+1 < q := by { dsimp [k] at *; omega };
        have hjq : k-j < q := by { dsimp [k] at *; omega }; have h1 := ih (j+1) hiq hpi (by { dsimp [k] at *; omega });
        have h2 := ih (k-j) hjq hpj (by { dsimp [k] at *; omega }); rw [wedge_trans hpactive h1 h2, mul_zero] } };
    have heq := hsys k hk.1 hk.2; rw [Finset.sum_eq_single_of_mem (p-1) hpterm hother] at heq; have hindex1 : p-1+1=p := by { omega };
    have hindex2 : k-(p-1)=q := by { dsimp [k]; omega }; rw [hindex1,hindex2] at heq;
    exact (mul_eq_zero.mp heq).resolve_left (hw k (p-1) hk.1 hk.2 (Finset.mem_range.mp hpterm)) } }
private theorem triangular_minors {u v : ℕ → ℂ} {weight : ℕ → ℕ → ℂ} {N : ℕ} (hw : ∀ k i, 2 ≤ k → k ≤ N → i < k / 2 → weight k i ≠ 0) (hsys : ∀ k, 2 ≤ k → k ≤ N → ∑ j ∈ Finset.range (k / 2), weight k j * wedge u v (j+1) (k-j) = 0) : ∀ i j, 1 ≤ i → i < j → i+j ≤ N+1 → wedge u v i j = 0 := by {
  classical {
    by_cases he : ∃ p, 1 ≤ p ∧ (u p ≠ 0 ∨ v p ≠ 0);
    · {
      let p := Nat.find he; have hp : 1 ≤ p ∧ (u p ≠ 0 ∨ v p ≠ 0) := Nat.find_spec he;
      have hbefore : ∀ i, 1 ≤ i → i < p → u i = 0 ∧ v i = 0 := by { intro i hi hip; have hh := Nat.find_min he hip; push Not at hh; exact hh hi };
      have hprop := triangular_pivot hp.1 hp.2 hbefore hw hsys; intro i j hi hij hijN; by_cases hip : i < p;
      · { obtain ⟨hu,hv⟩ := hbefore i hi hip; simp [wedge,hu,hv] };
      · { have hpj := hprop j (by { omega }) (by { omega }); by_cases heq : p=i; · { simpa [heq] using hpj }; · { exact wedge_trans hp.2 (hprop i (by { omega }) (by { omega })) hpj } } };
    · { intro i j hi hij hijN; have hu : u i = 0 := by { by_contra h; exact he ⟨i,hi,Or.inl h⟩ }; have hv : v i = 0 := by { by_contra h; exact he ⟨i,hi,Or.inr h⟩ }; simp [wedge,hu,hv] } } }
end Draft
private theorem phaseAt_ne {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, a i ≠ 0) (j : ℕ) : phaseAt a j ≠ 0 := by { unfold phaseAt; split <;> simp_all }
private theorem bracket_normalize {n : ℕ} {a x y : Fin n → ℂ} (ha : ∀ i, a i ≠ 0) (i j : ℕ) : Draft.wedge (fun k => phaseAt a k * phaseAt x k) (phaseAt y) i j = phaseAt a i * bracket a x y i j := by { dsimp [Draft.wedge, bracket]; field_simp [phaseAt_ne ha i] }
private theorem alpha_triangular {n : ℕ} {a b x y : Fin n → ℂ} (ha : ∀ i, a i ≠ 0) (h : BilinearSystem a b x y) : ∀ i j, 1 ≤ i → i < j → i+j ≤ n+1 → bracket a x y i j = 0 := by {
  have hw : ∀ k i, 2 ≤ k → k ≤ n → i < k/2 → (-1 : ℂ)^i * (phaseAt a (i+1))⁻¹ ≠ 0 := by { intros; exact mul_ne_zero (pow_ne_zero _ (by { norm_num })) (inv_ne_zero (phaseAt_ne ha _)) };
  have hs : ∀ k, 2 ≤ k → k ≤ n → ∑ j ∈ Finset.range (k/2), ((-1 : ℂ)^j * (phaseAt a (j+1))⁻¹) * Draft.wedge (fun i => phaseAt a i * phaseAt x i) (phaseAt y) (j+1) (k-j) = 0 := by { intro k hk hkn; convert h.1 k (Finset.mem_Icc.mpr ⟨hk,hkn⟩) using 1; apply Finset.sum_congr rfl; intro j hj; rw [bracket_normalize ha]; field_simp [phaseAt_ne ha (j+1)] };
  intro i j hi hij hijn; have hminor := Draft.triangular_minors hw hs i j hi hij hijn; rw [bracket_normalize ha] at hminor;
  exact (mul_eq_zero.mp hminor).resolve_left (phaseAt_ne ha _) }
private theorem beta_triangular {n : ℕ} {a b x y : Fin n → ℂ} (hb : ∀ i, b i ≠ 0) (h : BilinearSystem a b x y) : ∀ i j, 1 ≤ i → i < j → j ≤ n → n+1 < i+j → bracket b x y i j = 0 := by {
  let u : ℕ → ℂ := fun i => phaseAt b (n+1-i) * phaseAt x (n+1-i); let v : ℕ → ℂ := fun i => phaseAt y (n+1-i);
  let wt : ℕ → ℕ → ℂ := fun k j => -(-1 : ℂ)^j * (phaseAt b (n+1-(k-j)))⁻¹;
  have hw : ∀ k i, 2 ≤ k → k ≤ n-1 → i < k/2 → wt k i ≠ 0 := by { intros; exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (by { norm_num }))) (inv_ne_zero (phaseAt_ne hb _)) };
  have hs : ∀ k, 2 ≤ k → k ≤ n-1 → ∑ j ∈ Finset.range (k/2), wt k j * Draft.wedge u v (j+1) (k-j) = 0 := by {
    intro k hk hkn; have heq := h.2 (k-1) (Finset.mem_Icc.mpr (show 1 ≤ k-1 ∧ k-1 ≤ n-2 by { omega })); have hkm : k-1+1=k := by { omega }; rw [hkm] at heq;
    convert heq using 1; apply Finset.sum_congr rfl; intro j hj; have hjlt := Finset.mem_range.mp hj; have hi : n+1-(k-j) = n-(k-1)+j := by { omega };
    have hjj : n+1-(j+1) = n-j := by { omega };
    have hrev : Draft.wedge u v (j+1) (k-j) = -Draft.wedge (fun i => phaseAt b i * phaseAt x i) (phaseAt y) (n-(k-1)+j) (n-j) := by { dsimp [Draft.wedge,u,v]; rw [hi,hjj]; ring };
    rw [hrev,bracket_normalize hb]; dsimp [wt]; rw [hi]; field_simp [phaseAt_ne hb (n-(k-1)+j)] };
  intro i j hi hij hjn hijN; have h := Draft.triangular_minors hw hs (n+1-j) (n+1-i) (by { omega }) (by { omega }) (by { omega });
  have hci : n+1-(n+1-i)=i := by { omega }; have hcj : n+1-(n+1-j)=j := by { omega };
  have hr : Draft.wedge u v (n+1-j) (n+1-i) = -Draft.wedge (fun i => phaseAt b i * phaseAt x i) (phaseAt y) i j := by { dsimp [Draft.wedge,u,v]; rw [hci,hcj]; ring };
  rw [hr,neg_eq_zero,bracket_normalize hb] at h; exact (mul_eq_zero.mp h).resolve_left (phaseAt_ne hb _) }
private theorem finite_triangles {n : ℕ} {a b x y : Fin n → ℂ} (hg : GenericPhases a b) (h : BilinearSystem a b x y) : (∀ i j : Fin n, i.val+j.val+2 ≤ n+1 → Draft.wedge (fun k => a k * x k) y i j = 0) ∧ (∀ i j : Fin n, n+1 < i.val+j.val+2 → Draft.wedge (fun k => b k * x k) y i j = 0) := by {
  have he (c : Fin n → ℂ) (i j : Fin n) : Draft.wedge (fun k => phaseAt c k * phaseAt x k) (phaseAt y) (i.val+1) (j.val+1) = Draft.wedge (fun k => c k * x k) y i j := by { simp [Draft.wedge,phaseAt] };
  have ha : ∀ i, a i ≠ 0 := fun i => (hg.1 i).1; have hb : ∀ i, b i ≠ 0 := fun i => (hg.1 i).2;
  have az (i j : Fin n) (hij : i < j) (hs : i.val+j.val+2 ≤ n+1) : Draft.wedge (fun k => a k * x k) y i j = 0 := by { have ht := alpha_triangular ha h (i.val+1) (j.val+1) (by { omega }) (by { exact Nat.add_lt_add_right hij 1 }) (by { omega }); have hh := bracket_normalize (x := x) (y := y) ha (i.val+1) (j.val+1); rw [he,ht,mul_zero] at hh; exact hh };
  have bz (i j : Fin n) (hij : i < j) (hs : n+1 < i.val+j.val+2) : Draft.wedge (fun k => b k * x k) y i j = 0 := by { have ht := beta_triangular hb h (i.val+1) (j.val+1) (by { omega }) (by { exact Nat.add_lt_add_right hij 1 }) (by { omega }) (by { omega }); have hh := bracket_normalize (x := x) (y := y) hb (i.val+1) (j.val+1); rw [he,ht,mul_zero] at hh; exact hh };
  constructor;
  · { intro i j hs; rcases lt_trichotomy i j with hij | hij | hij; · { exact az i j hij hs }; · { subst j; simp [Draft.wedge] }; · { have hh := az j i hij (by { omega }); dsimp [Draft.wedge] at *; linear_combination -hh } };
  · { intro i j hs; rcases lt_trichotomy i j with hij | hij | hij; · { exact bz i j hij hs }; · { subst j; simp [Draft.wedge] }; · { have hh := bz j i hij (by { omega }); dsimp [Draft.wedge] at *; linear_combination -hh } } }
private theorem coordinates_from_pivot {ι : Type*} {a x y : ι → ℂ} {p : ι} (ha : ∀ i, a i ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) (hp : x p ≠ 0 ∨ y p ≠ 0) (hm : ∀ i, Draft.wedge (fun k => a k * x k) y p i = 0) : ∃ (c : ι → ℂ) (t : ℂ), t ≠ 0 ∧ (∀ i, c i ≠ 0 ↔ x i ≠ 0 ∨ y i ≠ 0) ∧ (∀ i, x i = c i * t ∧ y i = c i * a i) := by {
  have hxp : x p ≠ 0 := by { intro he; have hyp := hp.resolve_left (not_not_intro he); apply hx; funext i; have hh := hm i; simp [Draft.wedge,he,ha i,hyp] at hh; exact hh };
  have hyp : y p ≠ 0 := by { intro he; apply hy; funext i; have hh := hm i; simp [Draft.wedge,he,ha p,hxp] at hh; exact hh };
  let c : ι → ℂ := fun i => y i / a i; let t : ℂ := a p * x p / y p; have ht : t ≠ 0 := div_ne_zero (mul_ne_zero (ha p) hxp) hyp;
  have hc : ∀ i, x i = c i * t ∧ y i = c i * a i := by { intro i; constructor; · { dsimp [c,t]; field_simp [ha i,hyp]; have hh := hm i; dsimp [Draft.wedge] at hh; linear_combination -hh }; · { dsimp [c]; field_simp [ha i] } };
  refine ⟨c,t,ht,?_,hc⟩; intro i; rw [(hc i).1,(hc i).2]; simp [mul_ne_zero,ht,ha i] }
private theorem unequal_ratio_cross_zero {n : ℕ} {a b x y : Fin n → ℂ} (hg : GenericPhases a b) {i j : Fin n} (hij : i < j) (ha : Draft.wedge (fun k => a k*x k) y i j = 0) (hb : Draft.wedge (fun k => b k*x k) y i j = 0) : x i * y j = 0 ∧ x j * y i = 0 := by {
  have hratio : a j*b i ≠ b j*a i := by { intro he; apply hg.2 i j hij; field_simp [(hg.1 i).1,(hg.1 i).2]; simpa [mul_comm] using he };
  have hz : (a j*b i-b j*a i)*(x j*y i)=0 := by { dsimp [Draft.wedge] at *; linear_combination -b i*ha+a i*hb };
  have h2 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hratio); refine ⟨?_,h2⟩;
  have hz : a i*(x i*y j)=0 := by { dsimp [Draft.wedge] at ha; linear_combination ha+a j*h2 }; exact (mul_eq_zero.mp hz).resolve_left (hg.1 i).1 }
private theorem classified_of_triangles {n : ℕ} {a b x y : Fin n → ℂ} (hg : GenericPhases a b) (hA : ∀ i j : Fin n, i.val+j.val+2 ≤ n+1 → Draft.wedge (fun k => a k*x k) y i j = 0) (hB : ∀ i j : Fin n, n+1 < i.val+j.val+2 → Draft.wedge (fun k => b k*x k) y i j = 0) : Classified a b x y := by {
  classical {
    by_cases hx : x=0; · { exact Or.inl hx }; by_cases hy : y=0; · { exact Or.inr (Or.inl hy) }; right; right;
    let s : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0 ∨ y i ≠ 0); have hmem (i : Fin n) : i ∈ s ↔ x i ≠ 0 ∨ y i ≠ 0 := by { simp [s] };
    have hs : s.Nonempty := by { by_contra he; apply hx; funext i; have hh : ¬(x i ≠ 0 ∨ y i ≠ 0) := by { intro hh; exact he ⟨i,(hmem i).mpr hh⟩ }; simpa using (not_or.mp hh).1 };
    let p := s.min' hs; let q := s.max' hs; have hp : p ∈ s := Finset.min'_mem s hs; have hq : q ∈ s := Finset.max'_mem s hs;
    have hmin (i) (hi : i ∈ s) : p ≤ i := Finset.min'_le s i hi; have hmax (i) (hi : i ∈ s) : i ≤ q := Finset.le_max' s i hi;
    have hzero (i) (hi : i ∉ s) : x i=0 ∧ y i=0 := by { have hh : ¬(x i ≠ 0 ∨ y i ≠ 0) := fun hh => hi ((hmem i).mpr hh); simpa using hh };
    by_cases hpq : p.val+q.val+2 ≤ n+1;
    · {
      have hm : ∀ i, Draft.wedge (fun k => a k*x k) y p i=0 := by { intro i; by_cases hi : i ∈ s; · { exact hA p i (by { have := hmax i hi; omega }) }; · { obtain ⟨hxi,hyi⟩ := hzero i hi; simp [Draft.wedge,hxi,hyi] } };
      obtain ⟨c,t,ht,hc,hcoord⟩ := coordinates_from_pivot (fun i => (hg.1 i).1) hx hy ((hmem p).mp hp) hm;
      have hqboth : x q ≠ 0 ∧ y q ≠ 0 := by { have hcq : c q ≠ 0 := (hc q).mpr ((hmem q).mp hq); rw [(hcoord q).1,(hcoord q).2]; exact ⟨mul_ne_zero hcq ht,mul_ne_zero hcq (hg.1 q).1⟩ };
      have hallowed : AllowedSupport n true s := by {
        dsimp [AllowedSupport]; by_cases hsmall : 2*(q.val+1) ≤ n+1; · { left; intro i hi; have := hmax i hi; omega };
        · {
          right; refine ⟨p,q,hp,hq,hpq,?_,by { omega },?_⟩; · { omega };
          · {
            intro i hi; by_cases he : i=q; · { exact Or.inl he };
            · {
              right; refine ⟨hmin i hi,?_⟩; by_contra hsum; have hiq : i < q := lt_of_le_of_ne (hmax i hi) he;
              have htA := Draft.wedge_trans (u := fun k => a k*x k) (v := y) (p := p) (Or.inl (mul_ne_zero (hg.1 p).1 (show x p ≠ 0 by { have hh := (hc p).mpr ((hmem p).mp hp); rw [(hcoord p).1]; exact mul_ne_zero hh ht }))) (hm i) (hm q);
              have htB := hB i q (by { omega }); have hz := unequal_ratio_cross_zero hg hiq htA htB;
              have hxi : x i=0 := (mul_eq_zero.mp hz.1).resolve_right hqboth.2; have hyi : y i=0 := (mul_eq_zero.mp hz.2).resolve_left hqboth.1;
              exact (hmem i).mp hi |>.elim (fun hh => hh hxi) (fun hh => hh hyi) } } } };
      refine ⟨true,s,c,t,ht,hs,hallowed,?_,?_⟩; · { intro i; exact (hc i).trans (hmem i).symm }; · { simpa using hcoord } };
    · {
      have hm : ∀ i, Draft.wedge (fun k => b k*x k) y q i=0 := by { intro i; by_cases hi : i ∈ s; · { exact hB q i (by { have := hmin i hi; omega }) }; · { obtain ⟨hxi,hyi⟩ := hzero i hi; simp [Draft.wedge,hxi,hyi] } };
      obtain ⟨c,t,ht,hc,hcoord⟩ := coordinates_from_pivot (fun i => (hg.1 i).2) hx hy ((hmem q).mp hq) hm;
      have hpboth : x p ≠ 0 ∧ y p ≠ 0 := by { have hcp : c p ≠ 0 := (hc p).mpr ((hmem p).mp hp); rw [(hcoord p).1,(hcoord p).2]; exact ⟨mul_ne_zero hcp ht,mul_ne_zero hcp (hg.1 p).2⟩ };
      have hqactive : b q*x q ≠ 0 := by { have hcq : c q ≠ 0 := (hc q).mpr ((hmem q).mp hq); rw [(hcoord q).1]; exact mul_ne_zero (hg.1 q).2 (mul_ne_zero hcq ht) };
      have hallowed : AllowedSupport n false s := by {
        dsimp [AllowedSupport]; by_cases hlarge : n+1 ≤ 2*(p.val+1); · { left; intro i hi; have := hmin i hi; omega };
        · {
          right; refine ⟨p,q,hp,hq,by { omega },by { omega },?_,?_⟩; · { omega };
          · {
            intro i hi; by_cases he : i=p; · { exact Or.inl he };
            · {
              right; refine ⟨?_,hmax i hi⟩; by_contra hsum; have hpi : p < i := lt_of_le_of_ne (hmin i hi) (Ne.symm he); have htA := hA p i (by { omega });
              have htB := Draft.wedge_trans (u := fun k => b k*x k) (v := y) (p := q) (Or.inl hqactive) (hm p) (hm i);
              have hz := unequal_ratio_cross_zero hg hpi htA htB; have hyi : y i=0 := (mul_eq_zero.mp hz.1).resolve_left hpboth.1;
              have hxi : x i=0 := (mul_eq_zero.mp hz.2).resolve_right hpboth.2; exact (hmem i).mp hi |>.elim (fun hh => hh hxi) (fun hh => hh hyi) } } } };
      refine ⟨false,s,c,t,ht,hs,hallowed,?_,?_⟩; · { intro i; exact (hc i).trans (hmem i).symm }; · { simpa using hcoord } } } }
private theorem lemma33 : lemma33_statement := by { intro n hn a b x y hg h; obtain ⟨ha,hb⟩ := finite_triangles hg h; exact classified_of_triangles hg ha hb }
private theorem edge_from_range_interface {n : ℕ} (hn : 3 ≤ n) {a b w : Fin n → ℂ} {A : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)} (hg : GenericPhases a b) (hstar : StarCondition a b w) (hrange : ∀ x y : Fin n → ℂ, InRange (partialTranspose A) (tensor (fun i => conj (x i)) y) → BilinearSystem a b (fun i => conj (x i)) y) (hann : ∀ v : (Fin n × Fin n) → ℂ, InRange A v → ∑ i, v (i,i)*conj (w i)=0) : Edge A := by {
  intro x y hx hy hp; have hcx : (fun i => conj (x i)) ≠ 0 := by { intro he; apply hx; funext i; have hh := congrArg conj (congrFun he i); simpa using hh };
  have hclass := lemma33 n hn a b (fun i => conj (x i)) y hg (hrange x y hp.2); rcases hclass with he | he | ⟨isAlpha,s,c,t,ht,hs,ha,hc,hcoord⟩;
  · { exact hcx he }; · { exact hy he };
  have hnonzero := hstar isAlpha s hs ha (fun i => Complex.normSq (c i)) (fun i => Complex.normSq_nonneg (c i)) (by { intro i; simpa only [ne_eq,Complex.normSq_eq_zero] using hc i });
  have hdiag (i : Fin n) : x i*y i = conj t * ((Complex.normSq (c i) : ℂ)*(if isAlpha then a i else b i)) := by { have hh := congrArg conj (hcoord i).1; simp only [map_mul,starRingEnd_self_apply] at hh; rw [hh,(hcoord i).2,Complex.normSq_eq_conj_mul_self]; ring };
  have hh := hann (tensor x y) hp.1; simp only [tensor,Matrix.vecMulVec_apply,hdiag] at hh;
  have heq : (∑ i, conj t * ((Complex.normSq (c i) : ℂ)* (if isAlpha then a i else b i)) * conj (w i)) = conj t * ∑ i, ((Complex.normSq (c i) : ℂ)*(if isAlpha then a i else b i))* conj (w i) := by { rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring };
  rw [heq] at hh; exact hnonzero ((mul_eq_zero.mp hh).resolve_left (by { simpa using ht })) }

open Matrix
open scoped ComplexOrder
namespace Spectral
def pencil {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℂ) (s : ℝ) : Matrix ι ι ℂ := (s : ℂ) • 1 - A
theorem det_pencil {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (s : ℝ) : (pencil A s).det = ∏ i, ((s-hA.eigenvalues i : ℝ) : ℂ) := by {
  have hs : Matrix.scalar ι (s : ℂ) = (s : ℂ) • (1 : Matrix ι ι ℂ) := by { ext i j; by_cases hij : i=j <;> simp [Matrix.scalar,Matrix.diagonal,Matrix.one_apply,hij] };
  rw [pencil,←hs,←Matrix.eval_charpoly,hA.charpoly_eq];
  simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,Complex.ofReal_sub]; rfl }
theorem pencil_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (s : ℝ) : pencil A s = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary (diagonal (fun i => ((s-hA.eigenvalues i : ℝ) : ℂ))) := by {
  conv_lhs => rw [pencil,hA.spectral_theorem];
  have hh : (s : ℂ) • (1 : Matrix ι ι ℂ) - diagonal (fun i => (hA.eigenvalues i : ℂ)) = diagonal (fun i => ((s-hA.eigenvalues i : ℝ) : ℂ)) := by { ext i j; by_cases hij : i=j <;> simp [Matrix.diagonal,Matrix.one_apply,hij] };
  rw [←hh]; simp only [map_sub,map_smul,map_one]; rfl }
theorem largest_root_psd {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {r : ℝ} (hmax : ∀ s : ℝ, (pencil A s).det=0 → s ≤ r) : (pencil A r).PosSemidef := by {
  have hbound : ∀ i, hA.eigenvalues i ≤ r := by { intro i; apply hmax; rw [det_pencil hA]; exact Finset.prod_eq_zero (Finset.mem_univ i) (by { simp }) };
  rw [pencil_conjugate hA,Unitary.conjStarAlgAut_apply]; apply Matrix.PosSemidef.mul_mul_conjTranspose_same; apply Matrix.PosSemidef.diagonal; intro i;
  change (0 : ℂ) ≤ ((r-hA.eigenvalues i : ℝ) : ℂ); simp only [Complex.nonneg_iff,Complex.ofReal_re,Complex.ofReal_im];
  exact ⟨sub_nonneg.mpr (hbound i),True.intro⟩ }
theorem det_pencil_re {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (s : ℝ) : (pencil A s).det.re = ∏ i, (s-hA.eigenvalues i) := by { rw [det_pencil hA,←Complex.ofReal_prod,Complex.ofReal_re] }
private theorem simple_root_rank {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {r : ℝ} (hroot : (pencil A r).det=0) (hsimple : ∃ d : ℝ, d ≠ 0 ∧ HasDerivAt (fun s : ℝ => (pencil A s).det.re) d r) : (pencil A r).rank = Fintype.card ι-1 := by {
  classical {
    let f : ι → ℝ := fun i => r-hA.eigenvalues i; have hprod : ∏ i, f i = 0 := by { rw [←det_pencil_re hA,hroot]; rfl };
    obtain ⟨i,hi,hfi⟩ := Finset.prod_eq_zero_iff.mp hprod;
    have hder : HasDerivAt (fun s : ℝ => (pencil A s).det.re) (∑ i : ι, ∏ j ∈ Finset.univ.erase i, f j) r := by { have hh := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s => s-hA.eigenvalues i) (f' := fun _ => (1 : ℝ)) (fun i _ => (hasDerivAt_id r).sub_const (hA.eigenvalues i)); simpa only [f,smul_eq_mul,mul_one,←det_pencil_re hA] using hh };
    have hsum : (∑ i : ι, ∏ j ∈ Finset.univ.erase i, f j) ≠ 0 := by { obtain ⟨d,hd,hh⟩ := hsimple; exact fun he => hd (hh.unique hder |>.trans he) };
    have hunique : ∀ j, f j=0 → j=i := by {
      intro j hfj; by_contra hji; apply hsum; apply Finset.sum_eq_zero; intro k hk; by_cases hki : k=i;
      · { subst k; exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩) hfj };
      · { exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hki,Finset.mem_univ i⟩) hfi } };
    have heq : (fun j => f j=0) = (fun j => j=i) := by { funext j; exact propext ⟨hunique j,fun he => he ▸ hfi⟩ };
    have hcard : Fintype.card {j // f j=0}=1 := by { let e : {j // f j=0} ≃ {j // j=i} := Equiv.subtypeEquivRight (fun j => ⟨hunique j,fun he => he ▸ hfi⟩); exact (Fintype.card_congr e).trans (Fintype.card_subtype_eq i) };
    have hrank : (pencil A r).rank = (diagonal (fun i => ((f i : ℝ) : ℂ))).rank := by {
      rw [pencil_conjugate hA,Unitary.conjStarAlgAut_apply]; rw [←Unitary.coe_star];
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit (star hA.eigenvectorUnitary))];
      rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.UnitaryGroup.det_isUnit hA.eigenvectorUnitary)] };
    rw [hrank,Matrix.rank_diagonal]; let e : {j // (f j : ℂ) ≠ 0} ≃ {j // ¬f j=0} := Equiv.subtypeEquivRight (fun j => by { simp });
    rw [Fintype.card_congr e,Fintype.card_subtype_compl,hcard] } }
end Spectral
theorem D_hermitian {n : ℕ} (hn : 3 ≤ n) (a b : Fin n → ℂ) (r : ℝ) : (D a b r).IsHermitian := by { ext i j; simp only [Matrix.conjTranspose_apply]; dsimp [D]; split_ifs <;> simp_all [map_mul,map_ofNat,mul_comm,Complex.conj_ofReal] <;> try { omega <;> norm_num } }
theorem D_pencil {n : ℕ} (a b : Fin n → ℂ) (r : ℝ) : D a b r = Spectral.pencil (-D a b 0) r := by { ext i j; by_cases hij : i=j; · { subst j; simp [D,Spectral.pencil] }; · { simp [D,Spectral.pencil,Matrix.one_apply,hij] } }
private theorem D_largest_simple {n : ℕ} (hn : 3 ≤ n) {a b : Fin n → ℂ} {r : ℝ} (hr : LargestRoot a b r) (hs : SimpleRoot a b r) : (D a b r).PosSemidef ∧ (D a b r).rank=n-1 := by {
  have hH : (-D a b 0).IsHermitian := (D_hermitian hn a b 0).neg; constructor;
  · { rw [D_pencil]; exact Spectral.largest_root_psd hH (by { simpa only [←D_pencil] using hr.2 }) };
  · { rw [D_pencil]; simpa only [Fintype.card_fin] using Spectral.simple_root_rank hH (by { simpa only [←D_pencil] using hr.1 }) (by { simpa only [←D_pencil,SimpleRoot] using hs }) } }
set_option backward.isDefEq.respectTransparency false
namespace Partition
open Index
private theorem cycleBlock_psd_rank {n : ℕ} (hn : 3≤n) (a b : Fin n → ℂ) (ha : ∀ i, ‖a i‖=1) (hb : ∀ i, ‖b i‖=1) (t : Fin (2*n-3)) : (CycleBlock a b t).PosSemidef ∧ (CycleBlock a b t).rank=(addresses n t.val).length-1 := by {
  have hbounds := bounds hn t.isLt; have hlen := cycle_length hn t; have hz := blockZ_zero (show lo n t.val<hi n t.val by { omega }) (cyclePhase a b t.val);
  have hu : ∀ i, ‖cyclePhase a b t.val i‖=1 := by { intro i; unfold cyclePhase; split_ifs <;> first | { exact ha i } | { exact hb i } };
  have hu' : ∀ i : Fin (addresses n t.val).length, ‖blockZ (cyclePhase a b t.val) (betaUpper (hi n t.val) (lo n t.val)) i.val‖=1 := fun i=>blockZ_unit _ hu i.val;
  have hp := Cycle.P_psd hlen.1 hlen.2 hz hu'; constructor;
  · { unfold CycleBlock cycleScale; split_ifs; · { exact hp.smul (show (0:ℂ)≤2 by { norm_num }) }; · { simpa using hp } };
  · { rw [CycleBlock,Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero (by { unfold cycleScale; split_ifs <;> norm_num }))]; exact Cycle.P_rank hlen.1 hlen.2 hz (fun i=>norm_ne_zero_iff.mp (by { rw [hu' i]; norm_num })) } }
private theorem rhoGamma_psd_rank {n : ℕ} (hn : 3≤n) (a b : Fin n → ℂ) (r : ℝ) (ha : ∀ i, ‖a i‖=1) (hb : ∀ i, ‖b i‖=1) (hr : 0<r) : (rhoGamma a b r).PosSemidef ∧ (rhoGamma a b r).rank=n*n-2*n+3 := by {
  have hr' : (r:ℂ)≠0 := by { exact_mod_cast ne_of_gt hr };
  have hdiag : ((r:ℂ) • (1:Matrix (Fin n) (Fin n) ℂ)).rank=n := by { rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hr'),Matrix.rank_one,Fintype.card_fin] };
  have hp := fun t=>cycleBlock_psd_rank hn a b ha hb t; constructor;
  · { rw [←Matrix.posSemidef_submatrix_equiv (addressEquiv n hn),rhoGamma_reindex hn]; apply Blocks.psd_block; intro t; cases t with | none => { exact Matrix.PosSemidef.one.smul (show (0:ℂ)≤(r:ℂ) by { exact_mod_cast hr.le }) } | some t => { exact (hp t).1 } };
  · {
    rw [←Matrix.rank_submatrix _ (addressEquiv n hn) (addressEquiv n hn),rhoGamma_reindex hn, Blocks.rank_block];
    have htotal : n+(∑ t : Fin (2*n-3),(addresses n t.val).length)=n*n := by { have h : (∑ t, Fintype.card (Fin (dim n t)))=n*n := by { simpa only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin] using Fintype.card_congr (addressEquiv n hn) }; rw [Fintype.sum_option] at h; simpa only [dim,Fintype.card_fin] using h };
    have hsum : (∑ t : Fin (2*n-3),((CycleBlock a b t).rank+1)) = ∑ t : Fin (2*n-3),(addresses n t.val).length := by { apply Finset.sum_congr rfl; intro t ht; rw [(hp t).2]; have hh := (cycle_length hn t).1; omega };
    rw [Finset.sum_add_distrib] at hsum; simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hsum;
    have hopt : (∑ t,(GammaBlock a b r t).rank)=n+∑ t : Fin (2*n-3),(CycleBlock a b t).rank := by { rw [Fintype.sum_option]; change ((r:ℂ) • (1:Matrix (Fin n) (Fin n) ℂ)).rank+_=n+_; rw [hdiag]; rfl };
    rw [hopt]; omega } }
end Partition
namespace Partition
open Index
private theorem pEntry_swapped {lo hi i j : ℕ} (hlo : lo≤ i) (hhi : j≤hi) (hij : i<j) (hs : i+j=lo+hi) (z : ℕ→ℂ) (hz : z 0=1) (hu : ∀ k, k<(hi-lo+1)/2 → z k=1) : pEntry (2*((hi-lo+1)/2)) z (2*((hi-lo+1)/2)-1-(i-lo)) (i-lo) = if i=lo ∨ j≤ i+2 then (z (2*((hi-lo+1)/2)-1-(i-lo)))⁻¹ else 0 := by {
  let m := (hi-lo+1)/2; have hm : 0<m := by { dsimp [m]; omega }; have ht : i-lo<m := by { dsimp [m]; omega }; have hlt : i-lo<2*m-1-(i-lo) := by { omega };
  have hlast : 2*m-1-(i-lo)+1=2*m ↔ i=lo := by { omega }; have hadj : 2*m-1-(i-lo)=(i-lo)+1 ↔ j≤ i+2 := by { dsimp [m] at *; omega };
  have hfirst : ¬(2*m-1-(i-lo)=0 ∧ (i-lo)+1=2*m) := by { omega }; have hlast' : ((i-lo)=0 ∧ 2*m-1-(i-lo)+1=2*m) ↔ i=lo := by { omega };
  change (if 2*m-1-(i-lo)=i-lo then (if 2*m=2 then 1 else 2) else if i-lo=2*m-1-(i-lo)+1 then z (i-lo)/z (2*m-1-(i-lo)) else if 2*m-1-(i-lo)=(i-lo)+1 then z (i-lo)/z (2*m-1-(i-lo)) else if 2*m-1-(i-lo)=0 ∧ (i-lo)+1=2*m then z (i-lo) else if i-lo=0 ∧ 2*m-1-(i-lo)+1=2*m then (z (2*m-1-(i-lo)))⁻¹ else 0)=_;
  simp only [if_neg (by { omega } : ¬2*m-1-(i-lo)=i-lo), if_neg (by { omega } : ¬i-lo=2*m-1-(i-lo)+1),hu _ ht,one_div, if_neg hfirst,hadj,hlast'];
  by_cases ha : j≤ i+2 <;> simp [ha,m] }
private theorem blockEntry_swap {n lo hi : ℕ} (a : Fin n→ℂ) (c : ℂ) (i j : Fin n) (hlo : lo≤ i.val+1) (hhi : j.val+1≤hi) (hij : i<j) (hs : i.val+j.val+2=lo+hi) : blockEntry a (betaUpper hi lo) c (j,i) (i,j) = if i.val+1=lo ∨ j.val≤ i.val+2 then c*((phaseAt a (i.val+1))⁻¹*phaseAt a (j.val+1))⁻¹ else 0 := by {
  let m := (hi-lo+1)/2; let k := i.val+1-lo; have ht : k<m := by { dsimp [m,k]; omega }; have hm : 0<m := by { omega }; have hl : lo≤hi := by { omega };
  have hupper : (i.val+1,j.val+1)=(lo+k,hi-k) := by { dsimp [k]; congr 1 <;> omega };
  have hlower : (j.val+1,i.val+1)=(hi-k,lo+k) := by { dsimp [k]; congr 1 <;> omega }; have hiu := indices_idxOf_upper hl ht;
  have hil := indices_idxOf_lower (lo:=lo) (hi:=hi) (t:=2*m-1-k) hl (by { omega }) (by { omega }); have href : 2*m-1-(2*m-1-k)=k := by { omega };
  rw [href] at hil; have hmemu : (i.val+1,j.val+1)∈indexList (betaUpper hi lo) := by { apply (indices_mem hl).mpr; dsimp; omega };
  have hmeml : (j.val+1,i.val+1)∈indexList (betaUpper hi lo) := by { apply (indices_mem hl).mpr; dsimp; omega }; dsimp only [blockEntry];
  change (if (j.val+1,i.val+1)∈indexList (betaUpper hi lo) ∧ (i.val+1,j.val+1)∈indexList (betaUpper hi lo) then c*pEntry (indexList (betaUpper hi lo)).length (blockZ a (betaUpper hi lo)) ((indexList (betaUpper hi lo)).idxOf (j.val+1,i.val+1)) ((indexList (betaUpper hi lo)).idxOf (i.val+1,j.val+1)) else 0)=_;
  rw [if_pos ⟨hmeml,hmemu⟩,hupper,hlower,hiu,hil,indices_length]; have hz := blockZ_zero (show lo<hi by { omega }) a;
  have hu : ∀ q, q<m → blockZ a (betaUpper hi lo) q=1 := by { intro q hq; simp [blockZ,betaUpper,show q<(hi-lo+1)/2 from hq] };
  rw [pEntry_swapped hlo hhi (by { have h : i.val<j.val := hij; omega }) (by { omega }) _ hz hu];
  have hlen : 2*m-1-k<(indexList (betaUpper hi lo)).length := by { rw [indices_length]; dsimp [m] at *; omega };
  have hget := indices_get_lower lo hi (2*m-1-k) (by { omega }) (by { omega }); rw [href] at hget;
  have hidx : (indexList (betaUpper hi lo))[2*m-1-k]?=some (j.val+1,i.val+1) := by { change (indexList (betaUpper hi lo))[2*m-1-k]?=_; rw [List.getElem?_eq_getElem hlen,hget,←hlower] };
  have hzlower : blockZ a (betaUpper hi lo) (2*m-1-k) = (phaseAt a (i.val+1))⁻¹*phaseAt a (j.val+1) := by { unfold blockZ; rw [if_neg (by { simp [betaUpper]; dsimp [m] at *; omega }),hidx] };
  rw [hzlower]; split_ifs <;> simp_all <;> try { omega } }
end Partition
namespace Partition
open Index
set_option backward.isDefEq.respectTransparency false
private theorem cycleAddress_surj {n : ℕ} (hn : 3≤n) (t : Fin (2*n-3)) (row : (Fin n × Fin n)) (hnz : row.1≠row.2) (hs : row.1.val+row.2.val+2=t.val+3) : ∃ i,cycleAddress n hn t i=row := by {
  obtain ⟨⟨u,i⟩,he⟩ := Address_surjective hn row;
  cases u with | none => { change (i,i)=row at he; have h := congrArg Prod.fst he; have h' := congrArg Prod.snd he; exact (hnz (h.symm.trans h')).elim } | some u => { change cycleAddress n hn u i=row at he; have hu := cycleAddress_sum hn u i; rw [he] at hu; have hut : u=t := Fin.ext (by { omega }); subst u; exact ⟨i,he⟩ } }
private theorem rhoGamma_on_antidiagonal {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (t : Fin (2*n-3)) (row col : (Fin n × Fin n)) (hr : row.1≠row.2) (hc : col.1≠col.2) (hsr : row.1.val+row.2.val+2=t.val+3) (hsc : col.1.val+col.2.val+2=t.val+3) : rhoGamma a b r row col = blockEntry (cyclePhase a b t.val) (betaUpper (hi n t.val) (lo n t.val)) (cycleScale n t.val) row col := by { obtain ⟨i,rfl⟩ := cycleAddress_surj hn t row hr hsr; obtain ⟨j,rfl⟩ := cycleAddress_surj hn t col hc hsc; rw [rhoGamma_on_cycle,blockEntry_on_addresses]; rfl }
private theorem phaseAt_at {n : ℕ} (a : Fin n→ℂ) (i : Fin n) : phaseAt a (i.val+1)=a i := by { simp only [phaseAt,Nat.add_sub_cancel,Fin.eta,dif_pos i.isLt] }
private theorem rho_diagonal_upper_formula {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (i j : Fin n) (hij : i<j) : rho a b r (i,i) (j,j) = if i.val+j.val+1≤n then (if i.val=0 ∨ j.val≤ i.val+2 then cycleScale n (i.val+j.val-1)*(a i) * (a j)⁻¹ else 0) else (if j.val+1=n ∨ j.val≤ i.val+2 then cycleScale n (i.val+j.val-1)*(b i) * (b j)⁻¹ else 0) := by {
  let t : Fin (2*n-3) := ⟨i.val+j.val-1,by { have := i.isLt; have := j.isLt; omega }⟩; have ht : t.val+3=i.val+j.val+2 := by { dsimp [t]; omega };
  have hb := bounds hn t.isLt; have hl : lo n t.val≤ i.val+1 := by { dsimp [lo,t]; split_ifs <;> have := j.isLt <;> omega };
  have hh : j.val+1≤hi n t.val := by { dsimp [hi,t]; split_ifs <;> have := j.isLt <;> omega }; change rhoGamma a b r (j,i) (i,j)=_;
  rw [rhoGamma_on_antidiagonal hn a b r t (j,i) (i,j) (by { exact ne_of_gt hij }) (ne_of_lt hij) (by { dsimp; omega }) (by { dsimp; omega })];
  rw [blockEntry_swap _ _ _ _ hl hh hij (by { omega })]; simp only [phaseAt_at,_root_.mul_inv_rev,inv_inv]; by_cases hreg : i.val+j.val+1≤n;
  · { have hreg' : t.val+2≤n := by { dsimp [t]; omega }; simp only [cyclePhase,lo,if_pos hreg',if_pos hreg]; have hz : i.val+1=1 ↔ i.val=0 := by { omega }; simp only [hz]; split_ifs <;> dsimp [t] <;> ring };
  · { have hreg' : ¬t.val+2≤n := by { dsimp [t]; omega }; simp only [cyclePhase,lo,if_neg hreg',if_neg hreg]; have hz : i.val+1=t.val+3-n ↔ j.val+1=n := by { dsimp [t]; have := j.isLt; omega }; simp only [hz]; split_ifs <;> dsimp [t] <;> ring } }
end Partition
namespace Partition
open Index
set_option backward.isDefEq.respectTransparency false
private theorem rho_diagonal_upper_D {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (hab : Admissible a b) (i j : Fin n) (hij : i<j) : rho a b r (i,i) (j,j)=D a b r i j := by {
  have hi := i.isLt; have hj := j.isLt; have hij' : i.val<j.val := hij; have hijne : i≠j := ne_of_lt hij; have hj0 : j.val≠0 := by { omega };
  have hiN : i.val+1≠n := by { omega }; have hai : ∀ k, (a k)⁻¹=conj (a k) := fun k=>Complex.inv_eq_conj (hab.1 k).1;
  have hbi : ∀ k, (b k)⁻¹=conj (b k) := fun k=>Complex.inv_eq_conj (hab.1 k).2; rw [rho_diagonal_upper_formula hn a b r i j hij]; by_cases hi0 : i.val=0;
  · {
    have hreg : i.val+j.val+1≤n := by { omega };
    have ha0 : a i=1 := by { have hh := hab.2.1; rw [←show i.val+1=1 by { omega },phaseAt_at] at hh; exact hh };
    have hscale : cycleScale n (i.val+j.val-1)=if j.val=2 then 2 else 1 := by { unfold cycleScale; split_ifs <;> norm_num <;> omega };
    simp only [if_pos hreg,if_pos (Or.inl hi0),D,if_neg hijne,if_pos hi0,ha0,one_mul,mul_one,hai,hscale] };
  · {
    by_cases hjN : j.val+1=n;
    · {
      have hreg : ¬i.val+j.val+1≤n := by { omega };
      have hbN : b j=1 := by {
        calc
          b j = phaseAt b (j.val+1) := (phaseAt_at b j).symm
          _ = phaseAt b n := congrArg (phaseAt b) hjN
          _ = 1 := hab.2.2.1 };
      have hscale : cycleScale n (i.val+j.val-1)=if i.val+3=n then 2 else 1 := by { unfold cycleScale; split_ifs <;> norm_num <;> omega };
      simp only [if_neg hreg,if_pos (Or.inl hjN),D,if_neg hijne,if_neg hi0, if_neg hj0,if_pos hjN,hbN,inv_one,mul_one,hscale] };
    · {
      have hscale : cycleScale n (i.val+j.val-1)=1 := by { unfold cycleScale; rw [if_neg (by { omega })] };
      simp only [D,if_neg hijne,if_neg hi0,if_neg hj0,if_neg hjN,if_neg hiN,hscale, one_mul,hai,hbi];
      have hsmall : (i.val+1=j.val ∨ j.val+1=i.val ∨ i.val+2=j.val ∨ j.val+2=i.val) ↔ j.val≤ i.val+2 := by { omega }; simp only [hsmall];
      split_ifs <;> simp_all } } }
end Partition
private theorem partialTranspose_hermitian {n : ℕ} {A : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)} (hA : A.IsHermitian) : (partialTranspose A).IsHermitian := by { apply Matrix.IsHermitian.ext; rintro ⟨i,j⟩ ⟨k,l⟩; exact hA.apply (k,j) (i,l) }
theorem partialTranspose_involutive {n : ℕ} (A : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) : partialTranspose (partialTranspose A)=A := by { rfl }
namespace Partition
open Index
set_option backward.isDefEq.respectTransparency false
private theorem rho_diagonal_D {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (hab : Admissible a b) (hr : 0<r) (i j : Fin n) : rho a b r (i,i) (j,j)=D a b r i j := by {
  have hR := partialTranspose_hermitian (rhoGamma_psd_rank hn a b r (fun k=>(hab.1 k).1) (fun k=>(hab.1 k).2) hr).1.isHermitian;
  rcases lt_trichotomy i j with hij | hij | hji; · { exact rho_diagonal_upper_D hn a b r hab i j hij };
  · { subst j; change rhoGamma a b r (i,i) (i,i)=D a b r i i; rw [rhoGamma_diagonal_entry hn a b r _ _ (Or.inl rfl)]; simp [D] };
  · {
    calc
      rho a b r (i,i) (j,j) = star (rho a b r (j,j) (i,i)) := (hR.apply _ _).symm
      _ = star (D a b r j i) := congrArg star (rho_diagonal_upper_D hn a b r hab j i hji)
      _ = D a b r i j := (D_hermitian hn a b r).apply i j } }
private theorem mulVec_diagonalLift {n : ℕ} (A : (Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)) (w : Fin n→ℂ) (row : (Fin n × Fin n)) : A.mulVec (Function.uncurry (Matrix.diagonal w)) row=∑ i,A row (i,i)*w i := by { simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Function.uncurry,Matrix.diagonal_apply]; apply Finset.sum_congr rfl; intro i hi; rw [Finset.sum_eq_single i]; · { simp }; · { intro j hj hji; simp [Ne.symm hji] }; · { simp } }
private theorem rho_kernel_lift {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (hab : Admissible a b) (hr : 0<r) (w : Fin n→ℂ) (hw : (D a b r).mulVec w=0) : (rho a b r).mulVec (Function.uncurry (Matrix.diagonal w))=0 := by {
  funext ⟨i,j⟩; rw [mulVec_diagonalLift]; by_cases hij : i=j; · { subst j; simp_rw [rho_diagonal_D hn a b r hab hr]; exact congrFun hw i };
  · {
    apply Finset.sum_eq_zero; intro k hk; have hh := rho_diagonal_cross_zero a b r k i j hij;
    have hR := partialTranspose_hermitian (rhoGamma_psd_rank hn a b r (fun k=>(hab.1 k).1) (fun k=>(hab.1 k).2) hr).1.isHermitian;
    change (rho a b r).IsHermitian at hR; have hz := hR.apply (i,j) (k,k); rw [hh,star_zero] at hz; rw [←hz,zero_mul] } }
private theorem rho_range_annihilator {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (hab : Admissible a b) (hr : 0<r) (w : Fin n→ℂ) (hw : (D a b r).mulVec w=0) (v : (Fin n × Fin n)→ℂ) (hv : InRange (rho a b r) v) : ∑ i,v (i,i)*conj (w i)=0 := by {
  have hR := partialTranspose_hermitian (rhoGamma_psd_rank hn a b r (fun k=>(hab.1 k).1) (fun k=>(hab.1 k).2) hr).1.isHermitian;
  have hh := (Cycle.hermitian_range hR v).mp hv (Function.uncurry (Matrix.diagonal w)) (rho_kernel_lift hn a b r hab hr w hw);
  simpa [Function.uncurry,Matrix.diagonal_apply,apply_ite,Fintype.sum_prod_type,mul_comm] using hh }
end Partition
private theorem edge_from_star {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (hab : Admissible a b) (hr : 1<r) (w : Fin n→ℂ) (hw : (D a b r).mulVec w=0) (hstar : StarCondition a b w) : Edge (rho a b r) := by {
  apply edge_from_range_interface hn (w:=w) (a:=a) (b:=b);
  · { refine ⟨?_,hab.2.2.2⟩; intro i; constructor; · { exact norm_ne_zero_iff.mp (by { rw [(hab.1 i).1]; norm_num }) }; · { exact norm_ne_zero_iff.mp (by { rw [(hab.1 i).2]; norm_num }) } };
  · { exact hstar }; · { intro x y h; rw [rho,partialTranspose_involutive] at h; exact (range_reduction n hn a b x y r hab hr).mp h };
  · { intro v hv; exact Partition.rho_range_annihilator hn a b r hab (by { linarith }) w hw v hv } }
namespace Partition
open Index
set_option backward.isDefEq.respectTransparency false
private theorem indices_neighbor {lo hi u v : ℕ} (hl : lo<hi) (hu : u<(indexList (betaUpper hi lo)).length) (hv : v<(indexList (betaUpper hi lo)).length) (hn : v=u+1 ∨ u=v+1 ∨ (u=0 ∧ v+1=(indexList (betaUpper hi lo)).length) ∨ (v=0 ∧ u+1=(indexList (betaUpper hi lo)).length)) : let p := (indexList (betaUpper hi lo))[u]'hu; let q := (indexList (betaUpper hi lo))[v]'hv; p=q.swap ∨ (p.1+1=q.1 ∧ q.2+1=p.2) ∨ (q.1+1=p.1 ∧ p.2+1=q.2) := by {
  let m := (hi-lo+1)/2; have hm : 0<m := by { dsimp [m]; omega }; have hlu : u<2*m := by { simpa only [indices_length] using hu };
  have hlv : v<2*m := by { simpa only [indices_length] using hv }; simp only [indices_length] at hn; by_cases hum : u<m;
  · {
    rw [indices_get_upper lo hi u hum]; by_cases hvm : v<m;
    · { rw [indices_get_upper lo hi v hvm]; dsimp; rcases hn with h | h | h | h <;> first | { ({ right; omega }) } | { omega } };
    · { rw [indices_get_lower lo hi v (by { omega }) (by { omega })]; dsimp; left; apply Prod.ext <;> dsimp; all_goals { rcases hn with h | h | h | h <;> simp only [indices_length] at * <;> dsimp [m] at * <;> omega } } };
  · {
    rw [indices_get_lower lo hi u (by { omega }) (by { omega })]; by_cases hvm : v<m;
    · { rw [indices_get_upper lo hi v hvm]; dsimp; left; apply Prod.ext <;> dsimp; all_goals { rcases hn with h | h | h | h <;> simp only [indices_length] at * <;> dsimp [m] at * <;> omega } };
    · { rw [indices_get_lower lo hi v (by { omega }) (by { omega })]; dsimp; rcases hn with h | h | h | h <;> first | { ({ right; omega }) } | { omega } } } }
private theorem rhoGamma_support {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (row col : (Fin n × Fin n)) (hnz : rhoGamma a b r row col≠0) : row=col ∨ row=col.swap ∨ (row.1.val+1=col.1.val ∧ col.2.val+1=row.2.val) ∨ (col.1.val+1=row.1.val ∧ row.2.val+1=col.2.val) := by {
  by_cases hrow : row.1=row.2;
  · { have h := rhoGamma_diagonal_entry hn a b r row col (Or.inl hrow); rw [h] at hnz; split_ifs at hnz with he; · { exact Or.inl he.2 }; · { exact (hnz rfl).elim } };
  by_cases hcol : col.1=col.2;
  · { have h := rhoGamma_diagonal_entry hn a b r row col (Or.inr hcol); rw [h] at hnz; split_ifs at hnz with he; · { exact Or.inl he.2 }; · { exact (hnz rfl).elim } };
  have hneq : row.1.val≠row.2.val := fun he=>hrow (Fin.ext he);
  let t : Fin (2*n-3) := ⟨row.1.val+row.2.val-1,by { have := row.1.isLt; have := row.2.isLt; omega }⟩;
  have hsr : row.1.val+row.2.val+2=t.val+3 := by { dsimp [t]; omega };
  have hsc : col.1.val+col.2.val+2=t.val+3 := by { have he : row.1.val+row.2.val=col.1.val+col.2.val := by { by_contra hh; exact hnz (rhoGamma_antidiagonal a b r row col hh) }; omega };
  obtain ⟨i,hri⟩ := cycleAddress_surj hn t row hrow hsr; obtain ⟨j,hcj⟩ := cycleAddress_surj hn t col hcol hsc; rw [←hri,←hcj,rhoGamma_on_cycle] at hnz;
  change cycleScale n t.val*pEntry (addresses n t.val).length _ i.val j.val≠0 at hnz; have hp := (mul_ne_zero_iff.mp hnz).2;
  have hadj : i.val=j.val ∨ j.val=i.val+1 ∨ i.val=j.val+1 ∨ (i.val=0 ∧ j.val+1=(addresses n t.val).length) ∨ (j.val=0 ∧ i.val+1=(addresses n t.val).length) := by { unfold pEntry at hp; split_ifs at hp <;> tauto };
  rcases hadj with he | he; · { left; have hij : i=j := Fin.ext he; rw [←hri,←hcj,hij] };
  · {
    have hh := indices_neighbor (show lo n t.val<hi n t.val by { have := bounds hn t.isLt; omega }) i.isLt j.isLt he;
    have hi := (cycleAddress_values hn t i).symm; have hj := (cycleAddress_values hn t j).symm; rw [hri] at hi; rw [hcj] at hj;
    change (addresses n t.val)[i.val]=_ at hi; change (addresses n t.val)[j.val]=_ at hj;
    have heq : indexList (betaUpper (Partition.hi n t.val) (lo n t.val))=addresses n t.val := rfl; simp only [heq] at hh; rw [hi,hj] at hh; dsimp at hh;
    rcases hh with hh | hh | hh;
    · { right; left; apply Prod.ext <;> apply Fin.ext; · { have he := congrArg Prod.fst hh; dsimp at he ⊢; omega }; · { have he := congrArg Prod.snd hh; dsimp at he ⊢; omega } };
    · { exact Or.inr (Or.inr (Or.inl (by { omega }))) }; · { exact Or.inr (Or.inr (Or.inr (by { omega }))) } } }
end Partition
namespace Partition
set_option backward.isDefEq.respectTransparency false
private theorem rho_support {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (row col : (Fin n × Fin n)) (hnz : rho a b r row col≠0) : row=col ∨ (row.1=row.2 ∧ col.1=col.2) ∨ (row.1.val+1=col.1.val ∧ row.2.val+1=col.2.val) ∨ (col.1.val+1=row.1.val ∧ col.2.val+1=row.2.val) := by {
  have hh := rhoGamma_support hn a b r (col.1,row.2) (row.1,col.2) hnz; dsimp at hh; rcases hh with hh | hh | hh | hh;
  · { have h1 := congrArg (fun p : (Fin n × Fin n)=>p.1) hh; have h2 := congrArg (fun p : (Fin n × Fin n)=>p.2) hh; dsimp only at h1 h2; exact Or.inl (Prod.ext h1.symm h2) };
  · { right; left; exact ⟨(congrArg Prod.snd hh).symm,congrArg Prod.fst hh⟩ }; · { exact Or.inr (Or.inr (Or.inr hh)) };
  · { exact Or.inr (Or.inr (Or.inl hh)) } }
end Partition
namespace Partition
open Index
set_option backward.isDefEq.respectTransparency false
private theorem pEntry_norm {d : ℕ} (z : ℕ→ℂ) (hz : ∀ i : Fin d,‖z i.val‖=1) (i j : Fin d) (hij : i≠j) : ‖pEntry d z i.val j.val‖≤1 := by { have hij' : i.val≠j.val := fun he=>hij (Fin.ext he); unfold pEntry; split_ifs <;> simp [norm_div,norm_inv,hz i,hz j] <;> contradiction }
private theorem cycleScale_one_of_not_swap {n : ℕ} (hn : 3≤n) (t : Fin (2*n-3)) (i j : Fin (addresses n t.val).length) (hne : cycleAddress n hn t i≠cycleAddress n hn t j) (hswap : cycleAddress n hn t i≠(cycleAddress n hn t j).swap) : cycleScale n t.val=1 := by {
  unfold cycleScale; split_ifs with hspecial;
  · {
    exfalso; have hb := bounds hn t.isLt; have hsmall : hi n t.val≤lo n t.val+2 := by { dsimp [lo,hi]; split_ifs <;> omega };
    have hu := upper_single hb.2.1 hsmall;
    have hind : addresses n t.val=[(lo n t.val,hi n t.val),(hi n t.val,lo n t.val)] := by { simp [addresses,indexList,hu] };
    have hpi := List.getElem_mem i.isLt; have hpj := List.getElem_mem j.isLt; have hi := cycleAddress_values hn t i; have hj := cycleAddress_values hn t j;
    rw [←hi] at hpi; rw [←hj] at hpj; rw [hind] at hpi hpj; simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hpi hpj;
    rcases hpi with hpi | hpi <;> rcases hpj with hpj | hpj;
    all_goals { first | { apply hne; apply Prod.ext <;> apply Fin.ext <;> omega } | { apply hswap; apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega } } };
  · { rfl } }
private theorem rhoGamma_offdiag_norm {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (ha : ∀ i,‖a i‖=1) (hb : ∀ i,‖b i‖=1) (row col : (Fin n × Fin n)) (hne : row≠col) (hswap : row≠col.swap) : ‖rhoGamma a b r row col‖≤1 := by {
  by_cases hz : rhoGamma a b r row col=0; · { simp [hz] }; by_cases hrow : row.1=row.2;
  · { rw [rhoGamma_diagonal_entry hn a b r _ _ (Or.inl hrow)]; simp [hne] }; by_cases hcol : col.1=col.2;
  · { rw [rhoGamma_diagonal_entry hn a b r _ _ (Or.inr hcol)]; simp [hne] }; have hneq : row.1.val≠row.2.val := fun he=>hrow (Fin.ext he);
  let t : Fin (2*n-3) := ⟨row.1.val+row.2.val-1,by { have := row.1.isLt; have := row.2.isLt; omega }⟩;
  have hsr : row.1.val+row.2.val+2=t.val+3 := by { dsimp [t]; omega };
  have hsc : col.1.val+col.2.val+2=t.val+3 := by { have he : row.1.val+row.2.val=col.1.val+col.2.val := by { by_contra hh; exact hz (rhoGamma_antidiagonal a b r row col hh) }; omega };
  obtain ⟨i,hri⟩ := cycleAddress_surj hn t row hrow hsr; obtain ⟨j,hcj⟩ := cycleAddress_surj hn t col hcol hsc; rw [←hri,←hcj,rhoGamma_on_cycle];
  have hs := cycleScale_one_of_not_swap hn t i j (by { simpa [hri,hcj] using hne }) (by { simpa [hri,hcj] using hswap });
  change ‖cycleScale n t.val*pEntry (addresses n t.val).length _ i.val j.val‖≤1; rw [hs,one_mul]; apply pEntry_norm;
  · { intro k; apply blockZ_unit; intro k; unfold cyclePhase; split_ifs <;> first | { exact ha k } | { exact hb k } };
  · { intro he; exact hne (by { rw [←hri,←hcj,he] }) } }
end Partition
namespace Partition
open Index
set_option backward.isDefEq.respectTransparency false
private theorem rho_offdiag_diagonal {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (row : (Fin n × Fin n)) (hne : row.1≠row.2) : rho a b r row row = if row.1.val+row.2.val=1 ∨ row.1.val+row.2.val+3=2*n then 1 else 2 := by {
  have hneq : row.1.val≠row.2.val := fun he=>hne (Fin.ext he);
  let t : Fin (2*n-3) := ⟨row.1.val+row.2.val-1,by { have := row.1.isLt; have := row.2.isLt; omega }⟩;
  have hsr : row.1.val+row.2.val+2=t.val+3 := by { dsimp [t]; omega }; obtain ⟨i,hri⟩ := cycleAddress_surj hn t row hne hsr;
  change rhoGamma a b r row row=_; rw [←hri,rhoGamma_on_cycle]; change cycleScale n t.val*pEntry (addresses n t.val).length _ i.val i.val = _;
  simp only [pEntry,if_pos rfl]; have hsmall : (addresses n t.val).length=2 ↔ (hi n t.val-lo n t.val+1)/2=1 := by { rw [addresses,indices_length]; omega };
  simp only [hsmall]; rw [hri]; have hsum : row.1.val+row.2.val=t.val+1 := by { omega }; rw [hsum]; dsimp [cycleScale,lo,hi]; have ht := t.isLt;
  split_ifs <;> norm_num at * <;> omega }
private theorem rho_offdiag_norm {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (ha : ∀ i,‖a i‖=1) (hb : ∀ i,‖b i‖=1) (row col : (Fin n × Fin n)) (hr : row.1≠row.2) (hne : row≠col) : ‖rho a b r row col‖≤1 := by { apply rhoGamma_offdiag_norm hn a b r ha hb; · { intro h; apply hne; have h1 := congrArg Prod.fst h; have h2 := congrArg Prod.snd h; exact Prod.ext h1.symm h2 }; · { intro h; apply hr; have h2 := congrArg Prod.snd h; exact h2.symm } }
end Partition

open Matrix
open scoped ComplexOrder
namespace Path
theorem scaled_dominance_posDef {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (g : ι→ℂ) (hg : ∀ i,g i≠0) (hdd : ∀ i, (∑ j∈Finset.univ.erase i, ‖(g i)⁻¹*A i j*g j‖)<(A i i).re) : A.PosDef := by {
  apply hA.posDef_iff_eigenvalues_pos.mpr; intro k; let x : ι→ℂ := (hA.eigenvectorBasis k);
  have hx : x≠0 := by { exact (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero k) };
  let B := Matrix.diagonal (fun i=>(g i)⁻¹)*A*Matrix.diagonal g; let y : ι→ℂ := fun i=>(g i)⁻¹*x i;
  have hy : y≠0 := by { intro hz; apply hx; funext i; have hh := congrFun hz i; change (g i)⁻¹*x i=0 at hh; exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (hg i)) };
  have hmul : B.mulVec y=(hA.eigenvalues k : ℂ) • y := by {
    have hxy : (Matrix.diagonal g).mulVec y=x := by { funext i; simp [y,Matrix.mulVec_diagonal,hg i] };
    change (Matrix.diagonal (fun i=>(g i)⁻¹)*A*Matrix.diagonal g).mulVec y=_;
    rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hxy,hA.mulVec_eigenvectorBasis k]; funext i;
    simp only [Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul]; change (g i)⁻¹*((hA.eigenvalues k:ℂ)*x i)=(hA.eigenvalues k:ℂ)*((g i)⁻¹*x i); ring };
  have heig : Module.End.HasEigenvalue B.mulVecLin (hA.eigenvalues k:ℂ) := by { apply Module.End.hasEigenvalue_of_hasEigenvector (x:=y); exact ⟨(Module.End.mem_eigenspace_iff.mpr hmul),hy⟩ };
  obtain ⟨i,hi⟩ := eigenvalue_mem_ball heig; have hentry (i j : ι) : B i j=(g i)⁻¹*A i j*g j := by { simp [B,Matrix.mul_diagonal,Matrix.diagonal_mul] };
  have hdiag : B i i=A i i := by { rw [hentry]; field_simp [hg i] }; rw [Metric.mem_closedBall,dist_eq_norm,hdiag] at hi;
  have hbound := Complex.re_le_norm (A i i-(hA.eigenvalues k:ℂ)); simp only [Complex.sub_re,Complex.ofReal_re] at hbound;
  have hdd' : (∑ j∈Finset.univ.erase i,‖B i j‖)<(A i i).re := by { simpa only [hentry] using hdd i }; rw [norm_sub_rev] at hi; linarith }
end Path
namespace Path
theorem sum_indicator_le {ι : Type*} [Fintype ι] (P : ι→Prop) [DecidablePred P] (hP : ∀ i j,P i→P j→i=j) (c : ℝ) (hc : 0≤c) : (∑ i,if P i then c else 0)≤c := by {
  classical {
    rw [←Finset.sum_filter];
    have hcard : (Finset.univ.filter P).card≤1 := by { apply Finset.card_le_one.mpr; intro i hi j hj; exact hP i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 };
    rw [Finset.sum_const,nsmul_eq_mul]; have hh : ((Finset.univ.filter P).card:ℝ)≤1 := by { exact_mod_cast hcard }; nlinarith } }
end Path
namespace Partition
set_option backward.isDefEq.respectTransparency false
private def offWeight {n : ℕ} (p : {p : Fin n × Fin n // p.1 ≠ p.2}) : ℝ := ((p.val.1.val:ℝ)+1)*((n:ℝ)-(p.val.2.val:ℝ))
private theorem offWeight_pos {n : ℕ} (p : {p : Fin n × Fin n // p.1 ≠ p.2}) : 0<offWeight p := by { have h1 : 0≤(p.val.1.val:ℝ) := by { positivity }; have h2 : (p.val.2.val:ℝ)<n := by { exact_mod_cast p.val.2.isLt }; dsimp [offWeight]; positivity }
private theorem rho_near_diagonal_zero {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (row col : (Fin n × Fin n)) (hne : row≠col) (hnear : row.1.val+1=row.2.val ∨ row.2.val+1=row.1.val) : rho a b r row col=0 := by {
  by_contra hz; have hh := rho_support hn a b r row col hz;
  have hdiag : col.1=row.2 ∨ row.1=col.2 := by {
    rcases hh with he | he | he | he; · { exact (hne he).elim }; · { have hval := congrArg Fin.val he.1; omega };
    · { rcases hnear with hnear | hnear; · { left; apply Fin.ext; omega }; · { right; apply Fin.ext; omega } };
    · { rcases hnear with hnear | hnear; · { right; apply Fin.ext; omega }; · { left; apply Fin.ext; omega } } };
  have hgneq : (col.1,row.2)≠(row.1,col.2) := by { intro he; apply hne; have h1 := congrArg Prod.fst he; have h2 := congrArg Prod.snd he; exact Prod.ext h1.symm h2 };
  change rhoGamma a b r (col.1,row.2) (row.1,col.2)≠0 at hz; rw [rhoGamma_diagonal_entry hn a b r _ _ hdiag] at hz; simp [hgneq] at hz }
private theorem rho_offdiag_posDef {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (hab : Admissible a b) (hr : 0<r) : ((rho a b r).submatrix (fun p : {p : Fin n × Fin n // p.1 ≠ p.2}=>p.val) (fun p=>p.val)).PosDef := by {
  let A : Matrix ({p : Fin n × Fin n // p.1 ≠ p.2}) ({p : Fin n × Fin n // p.1 ≠ p.2}) ℂ := (rho a b r).submatrix Subtype.val Subtype.val;
  have hR : (rho a b r).IsHermitian := partialTranspose_hermitian (rhoGamma_psd_rank hn a b r (fun k=>(hab.1 k).1) (fun k=>(hab.1 k).2) hr).1.isHermitian;
  apply Path.scaled_dominance_posDef (A:=A) (hR.submatrix _) (fun p=>(offWeight p:ℂ)) (fun p=>by { exact_mod_cast ne_of_gt (offWeight_pos p) }); intro p;
  let u : ℝ := (p.val.1.val:ℝ); let v : ℝ := (p.val.2.val:ℝ); let N : ℝ := n; let gp : ℝ := u*(N-v+1); let gn : ℝ := (u+2)*(N-v-1);
  have hu : 0≤u := by { dsimp [u]; positivity }; have hv : v+1≤N := by { dsimp [v,N]; exact_mod_cast p.val.2.isLt };
  have hgp : 0≤gp := mul_nonneg hu (by { linarith }); have hgn : 0≤gn := mul_nonneg (by { linarith }) (by { linarith }); have hg := offWeight_pos p;
  have hgval : offWeight p=(u+1)*(N-v) := rfl; have hsum : gp+gn=2*offWeight p-2 := by { rw [hgval]; dsimp [gp,gn]; ring };
  let P : {p : Fin n × Fin n // p.1 ≠ p.2}→Prop := fun q=>q.val.1.val+1=p.val.1.val ∧ q.val.2.val+1=p.val.2.val;
  let T : {p : Fin n × Fin n // p.1 ≠ p.2}→Prop := fun q=>p.val.1.val+1=q.val.1.val ∧ p.val.2.val+1=q.val.2.val;
  have hunique (q s : {p : Fin n × Fin n // p.1 ≠ p.2}) (hq : P q) (hs : P s) : q=s := by { apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;> dsimp [P] at * <;> omega };
  have hunique' (q s : {p : Fin n × Fin n // p.1 ≠ p.2}) (hq : T q) (hs : T s) : q=s := by { apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;> dsimp [T] at * <;> omega };
  have hgwP (q : {p : Fin n × Fin n // p.1 ≠ p.2}) (hq : P q) : offWeight q=gp := by { have h1 : (q.val.1.val:ℝ)+1=u := by { dsimp [u]; exact_mod_cast hq.1 }; have h2 : (q.val.2.val:ℝ)+1=v := by { dsimp [v]; exact_mod_cast hq.2 }; dsimp [offWeight,gp,N]; rw [h1]; dsimp [v] at h2; nlinarith };
  have hgwT (q : {p : Fin n × Fin n // p.1 ≠ p.2}) (hq : T q) : offWeight q=gn := by { have h1 : u+1=(q.val.1.val:ℝ) := by { dsimp [u]; exact_mod_cast hq.1 }; have h2 : v+1=(q.val.2.val:ℝ) := by { dsimp [v]; exact_mod_cast hq.2 }; dsimp [offWeight,gn,N]; rw [←h1,←h2]; ring };
  have hterm (q : {p : Fin n × Fin n // p.1 ≠ p.2}) (hq : q≠p) : ‖(offWeight p:ℂ)⁻¹*A p q*(offWeight q:ℂ)‖≤ (if P q then gp/offWeight p else 0)+(if T q then gn/offWeight p else 0) := by {
    have hnorm := rho_offdiag_norm hn a b r (fun k=>(hab.1 k).1) (fun k=>(hab.1 k).2) p.val q.val p.property (fun he=>hq (Subtype.ext he).symm);
    have he : ‖(offWeight p:ℂ)⁻¹*A p q*(offWeight q:ℂ)‖= (offWeight p)⁻¹*‖rho a b r p.val q.val‖*offWeight q := by { simp [A,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs, abs_of_pos hg,abs_of_pos (offWeight_pos q)] };
    rw [he];
    have hle : (offWeight p)⁻¹*‖rho a b r p.val q.val‖*offWeight q≤offWeight q/offWeight p := by {
      rw [div_eq_mul_inv];
      calc
        _ ≤ (offWeight p)⁻¹*1*offWeight q := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hg.le)) (offWeight_pos q).le
        _ = _ := by { ring } };
    by_cases hP : P q; · { have hT : ¬T q := by { dsimp [P,T] at *; omega }; simpa only [if_pos hP,if_neg hT,add_zero,hgwP q hP] using hle };
    · {
      by_cases hT : T q; · { simpa only [if_neg hP,if_pos hT,zero_add,hgwT q hT] using hle };
      · {
        have hz : rho a b r p.val q.val=0 := by { by_contra hz; have hh := rho_support hn a b r p.val q.val hz; rcases hh with hh | hh | hh | hh; · { exact hq (Subtype.ext hh).symm }; · { exact p.property hh.1 }; · { exact hT hh }; · { exact hP hh } };
        simp [hz,if_neg hP,if_neg hT] } } };
  have hbound : (∑ q∈Finset.univ.erase p,‖(offWeight p:ℂ)⁻¹*A p q*(offWeight q:ℂ)‖)<2 := by {
    calc
      _ ≤ ∑ q∈Finset.univ.erase p, ((if P q then gp/offWeight p else 0)+(if T q then gn/offWeight p else 0)) := Finset.sum_le_sum (fun q hq=>hterm q (Finset.mem_erase.mp hq).1)
      _ ≤ ∑ q, ((if P q then gp/offWeight p else 0)+(if T q then gn/offWeight p else 0)) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by { intro q hq hq'; positivity })
      _ ≤ gp/offWeight p+gn/offWeight p := by { rw [Finset.sum_add_distrib]; exact add_le_add (Path.sum_indicator_le P hunique _ (div_nonneg hgp hg.le)) (Path.sum_indicator_le T hunique' _ (div_nonneg hgn hg.le)) }
      _ < 2 := by { rw [←add_div,hsum]; apply (div_lt_iff₀ hg).mpr; linarith } };
  change _ < (rho a b r p.val p.val).re; rw [rho_offdiag_diagonal hn a b r p.val p.property]; split_ifs with hs;
  · {
    have hnear : p.val.1.val+1=p.val.2.val ∨ p.val.2.val+1=p.val.1.val := by { have hi := p.val.1.isLt; have hj := p.val.2.isLt; have hh : p.val.1.val≠p.val.2.val := fun he=>p.property (Fin.ext he); omega };
    have hz : ∑ q∈Finset.univ.erase p,‖(offWeight p:ℂ)⁻¹*A p q*(offWeight q:ℂ)‖=0 := by { apply Finset.sum_eq_zero; intro q hq; have hqp := (Finset.mem_erase.mp hq).1; have he := rho_near_diagonal_zero hn a b r p.val q.val (fun he=>hqp (Subtype.ext he).symm) hnear; simp [A,he] };
    rw [hz]; norm_num };
  · { simpa using hbound } }
end Partition
namespace Partition
set_option backward.isDefEq.respectTransparency false
private def RhoCarrier (n : ℕ) (t : Bool) := bif t then {p : Fin n × Fin n // p.1 ≠ p.2} else Fin n
private def rhoAddress (n : ℕ) : (Σ t:Bool, RhoCarrier n t) ≃ (Fin n × Fin n) where toFun p := match p with | ⟨false,i⟩ => (i,i) | ⟨true,p⟩ => p.val; invFun p := if h:p.1=p.2 then ⟨false,p.1⟩ else ⟨true,⟨p,h⟩⟩; left_inv p := by { rcases p with ⟨t,p⟩; cases t; · { simp }; · { simp [p.property] } }; right_inv p := by { dsimp; split_ifs with h; · { exact Prod.ext rfl h }; · { rfl } }
private def RhoBlock {n : ℕ} (a b : Fin n→ℂ) (r : ℝ) : ∀ t:Bool, Matrix (RhoCarrier n t) (RhoCarrier n t) ℂ | false => D a b r | true => (rho a b r).submatrix Subtype.val Subtype.val
private theorem rho_reindex {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (hab : Admissible a b) (hr : 0<r) : (rho a b r).submatrix (rhoAddress n) (rhoAddress n)=Matrix.blockDiagonal' (RhoBlock a b r) := by {
  ext ⟨t,i⟩ ⟨s,j⟩; cases t <;> cases s; · { simp [rhoAddress,RhoBlock,Matrix.blockDiagonal',rho_diagonal_D hn a b r hab hr] };
  · { simp [rhoAddress,RhoBlock,Matrix.blockDiagonal',rho_diagonal_cross_zero a b r i j.val.1 j.val.2 j.property] };
  · {
    have hR := partialTranspose_hermitian (rhoGamma_psd_rank hn a b r (fun k=>(hab.1 k).1) (fun k=>(hab.1 k).2) hr).1.isHermitian;
    have he := hR.apply i.val (j,j); change star (rho a b r (j,j) (i.val.1,i.val.2))=rho a b r i.val (j,j) at he;
    rw [rho_diagonal_cross_zero a b r j i.val.1 i.val.2 i.property,star_zero] at he; simpa [rhoAddress,RhoBlock,Matrix.blockDiagonal'] using he.symm };
  · { simp [rhoAddress,RhoBlock,Matrix.blockDiagonal'] } }
private theorem rho_psd_rank {n : ℕ} (hn : 3≤n) (a b : Fin n→ℂ) (r : ℝ) (hab : Admissible a b) (hr : 0<r) (hd : (D a b r).PosSemidef) (hdrank : (D a b r).rank=n-1) : (rho a b r).PosSemidef ∧ (rho a b r).rank=n*n-1 := by {
  letI : ∀ t:Bool,Fintype (RhoCarrier n t) := fun t=>by { cases t <;> dsimp [RhoCarrier] <;> infer_instance };
  letI : ∀ t:Bool,DecidableEq (RhoCarrier n t) := fun t=>by { cases t <;> dsimp [RhoCarrier] <;> infer_instance };
  have hp := rho_offdiag_posDef hn a b r hab hr; constructor;
  · { rw [←Matrix.posSemidef_submatrix_equiv (rhoAddress n),rho_reindex hn a b r hab hr]; apply Blocks.psd_block; intro t; cases t; · { exact hd }; · { exact hp.posSemidef } };
  · {
    rw [←Matrix.rank_submatrix _ (rhoAddress n) (rhoAddress n),rho_reindex hn a b r hab hr, Blocks.rank_block];
    have ho : ((rho a b r).submatrix (fun p : {p : Fin n × Fin n // p.1 ≠ p.2}=>p.val) (fun p : {p : Fin n × Fin n // p.1 ≠ p.2}=>p.val)).rank= Fintype.card ({p : Fin n × Fin n // p.1 ≠ p.2}) := Matrix.rank_of_isUnit _ hp.isUnit;
    have hcard : n+Fintype.card ({p : Fin n × Fin n // p.1 ≠ p.2})=n*n := by { have h := Fintype.card_congr (rhoAddress n); simpa [Fintype.card_sigma,Fintype.sum_bool,RhoCarrier,Nat.add_comm] using h };
    rw [Fintype.sum_bool]; change ((rho a b r).submatrix (fun p : {p : Fin n × Fin n // p.1 ≠ p.2}=>p.val) (fun p : {p : Fin n × Fin n // p.1 ≠ p.2}=>p.val)).rank+(D a b r).rank=_; rw [hdrank,ho];
    omega } }
end Partition
theorem proposition61 : proposition61_statement := by {
  intro n hn a b r w hab hr hroot hsimple hw hker hstar; have hD := D_largest_simple hn hroot hsimple;
  have hR := Partition.rho_psd_rank hn a b r hab (by { linarith }) hD.1 hD.2;
  have hG := Partition.rhoGamma_psd_rank hn a b r (fun k=>(hab.1 k).1) (fun k=>(hab.1 k).2) (by { linarith });
  refine ⟨⟨hR.1,?_⟩,edge_from_star hn a b r hab hr w hker hstar,hR.2,hG.2⟩; simpa only [rho,partialTranspose_involutive] using hG.1 }


#print axioms range_reduction
#print axioms lemma33
#print axioms proposition61

end D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction
