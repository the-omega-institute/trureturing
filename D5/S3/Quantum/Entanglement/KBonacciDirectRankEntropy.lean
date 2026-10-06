/- GID: D5/S3/Quantum/Entanglement/KBonacciDirectRankEntropy
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/KBonacciDirectRankEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact auxiliary ranks and simultaneous entropy maxima for legal direct two-page encoders. -/

import D5.S3.Quantum.Entanglement.KBonacciDirectSupportObstruction
import D5.S1.Words.AdmissibleWords.KBonacciDirectConcatenation
import D5.S3.Quantum.Entanglement.UniversalReplacementCapacityGrowth
import D5.S3.Quantum.Information.InputInformationBalance
import D5.S3.Quantum.Information.OrthogonalRecordEntropy
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Sort
import Mathlib.Order.PiLex
import Mathlib.Data.Prod.Lex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
open D5.S0.Tower.DBonacci.Names
open D5.S1.Words.AdmissibleWords.KBonacciDirectConcatenation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Entanglement.KBonacciDirectRankEntropy

local instance (p : Prop) : Decidable p := Classical.propDecidable p

def primeNumbers (N : ℕ) (b : Bool) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun n => decide (Nat.Prime n.val) = b)

abbrev PrimePage (N : ℕ) (b : Bool) := ↥(primeNumbers N b)
abbrev Logical (N : ℕ) := Σ b : Bool, PrimePage N b
abbrev Word (m : ℕ) := Fin m → Bool

def initialRun {m : ℕ} (w : Fin m → Bool) : ℕ :=
  (List.ofFn w).findIdx Bool.not

def terminalRun {m : ℕ} (w : Fin m → Bool) : ℕ :=
  initialRun (fun i => w i.rev)

def oneNeighborhood (k n s : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun w => DBonacciAdmissible k n w ∧
    (List.ofFn w).head? = some true ∧ initialRun w < k - s)

def logicalDimension (N : ℕ) (b : Bool) : ℕ := (primeNumbers N b).card

def orderedNumbers (N : ℕ) (b : Bool) :
    Fin (logicalDimension N b) ≃o PrimePage N b :=
  (primeNumbers N b).orderIsoOfFin rfl

def wordPages (k m : ℕ) (b : Bool) : Finset (Word m) :=
  Finset.univ.filter (fun w => DBonacciAdmissible k m w ∧
    (List.ofFn w).head? = some b)

def capacity (k m : ℕ) (b : Bool) : ℕ := (wordPages k m b).card
def stateRows (k m s : ℕ) : ℕ :=
  ((wordPages k m true).filter (fun x => terminalRun x = s)).card
def earlierRows (k m s : ℕ) : ℕ := ∑ u ∈ Finset.range s, stateRows k m u
def neighborCount (k n s : ℕ) : ℕ := (oneNeighborhood k n s).card

def zeroMaximum (N k mX mY : ℕ) : ℕ :=
  min (capacity k mX false) (capacity k mY false / logicalDimension N false)

def oneMaximum (N k mX mY : ℕ) : ℕ :=
  ((List.range k).map (fun s =>
    earlierRows k mX s + neighborCount k mY s / logicalDimension N true)).foldl
      min (capacity k mX true)

def logicalProjection (N : ℕ) (b : Bool) : Matrix (Logical N) (Logical N) ℂ :=
  Matrix.diagonal (fun l => if l.1 = b then 1 else 0)

def physicalProjection (k m : ℕ) (b : Bool) : Matrix (Word m) (Word m) ℂ :=
  Matrix.diagonal (fun w => if w ∈ wordPages k m b then 1 else 0)

abbrev Encoder (N mX mY : ℕ) := Matrix (Word mX × Word mY) (Logical N) ℂ
abbrev PageStates (mX : ℕ) := Bool → DensityState (Word mX)

def directContract (N k mX mY : ℕ) (J : Encoder N mX mY) (sigma : PageStates mX) : Prop :=
  J.conjTranspose * J = 1 ∧
  (∀ b : Bool,
    (physicalProjection k mX b ⊗ₖ (1 : Matrix (Word mY) (Word mY) ℂ)) * J =
      J * logicalProjection N b ∧
    ((1 : Matrix (Word mX) (Word mX) ℂ) ⊗ₖ physicalProjection k mY b) * J =
      J * logicalProjection N b ∧
    physicalProjection k mX b * CStarMatrix.ofMatrix.symm (sigma b).val *
      physicalProjection k mX b = CStarMatrix.ofMatrix.symm (sigma b).val) ∧
  (∀ A : Matrix (Logical N) (Logical N) ℂ,
    partialTraceRight (J * A * J.conjTranspose) =
      ∑ b : Bool, Matrix.trace (logicalProjection N b * A) •
        CStarMatrix.ofMatrix.symm (sigma b).val) ∧
  (∀ (psi : Logical N → ℂ) (x : Word mX) (y : Word mY),
    ¬ DBonacciAdmissible k (mX + mY) (Fin.append x y) →
      (Matrix.mulVec J psi) (x, y) = 0)

variable {N mX mY : ℕ}

def pageRank (sigma : PageStates mX) (b : Bool) : ℕ :=
  Matrix.rank (CStarMatrix.ofMatrix.symm (sigma b).val)

def purePage (N : ℕ) (b : Bool) (psi : Logical N → ℂ) : Prop :=
  (∑ l, star (psi l) * psi l) = 1 ∧ ∀ l : Logical N, l.1 ≠ b → psi l = 0

def encodedSchmidtRank (J : Encoder N mX mY) (psi : Logical N → ℂ) : ℕ :=
  Matrix.rank (fun x y => (Matrix.mulVec J psi) (x, y))

def totalRowSpectralNecessity (N k mX mY : ℕ)
    (J : Encoder N mX mY) (sigma : PageStates mX) : Prop :=
  let hPos : (CStarMatrix.ofMatrix.symm (sigma true).val).PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (sigma true).property.1)
  let E := hPos.isHermitian.eigenvectorBasis
  let lam := hPos.isHermitian.eigenvalues
  let D := {j : Word mX // lam j ≠ 0}
  let q : Word mX → (D → ℂ) := fun x j => (Real.sqrt (lam j.val) : ℂ) * E j.val x
  ∃ W : Matrix (Word mY) (PrimePage N true × D) ℂ,
    W.conjTranspose * W = 1 ∧
    (∀ (r : PrimePage N true) (x : Word mX) (y : Word mY),
      J (x, y) ⟨true, r⟩ = ∑ j : D, q x j * W y (r, j)) ∧
    (∀ (r : PrimePage N true) (j : D) (y : Word mY),
      y ∉ wordPages k mY true → W y (r, j) = 0) ∧
    (Submodule.span ℂ (q '' (wordPages k mX true : Set (Word mX)))) = ⊤ ∧
    (∀ s : ℕ, s < k →
      let A := ((wordPages k mX true).filter (fun x => s ≤ terminalRun x) : Set (Word mX))
      let V := Submodule.span ℂ (q '' A)
      pageRank sigma true ≤ earlierRows k mX s + Module.finrank ℂ V ∧
      (∀ (r : PrimePage N true) (v : D → ℂ), v ∈ V → ∀ y : Word mY,
        y ∉ oneNeighborhood k mY s →
          ∑ j : D, W y (r, j) * v j = 0) ∧
      logicalDimension N true * Module.finrank ℂ V ≤ neighborCount k mY s)

def completeOriginal72 : Prop :=
  ∀ N k mX mY : ℕ, 2 ≤ N → 2 ≤ k → 1 ≤ mX → 1 ≤ mY →
  0 < logicalDimension N false ∧ 0 < logicalDimension N true ∧
  (∀ (J : Encoder N mX mY) (sigma : PageStates mX),
    directContract N k mX mY J sigma →
      pageRank sigma false ≤ zeroMaximum N k mX mY ∧
      pageRank sigma true ≤ oneMaximum N k mX mY ∧
      totalRowSpectralNecessity N k mX mY J sigma) ∧
  (∀ d0 d1 : ℕ,
    (∃ (J : Encoder N mX mY) (sigma : PageStates mX),
      directContract N k mX mY J sigma ∧
      pageRank sigma false = d0 ∧ pageRank sigma true = d1) ↔
    (1 ≤ d0 ∧ d0 ≤ zeroMaximum N k mX mY ∧
      1 ≤ d1 ∧ d1 ≤ oneMaximum N k mX mY)) ∧
  ((∃ (J : Encoder N mX mY) (sigma : PageStates mX),
    directContract N k mX mY J sigma) ↔
      1 ≤ zeroMaximum N k mX mY ∧ 1 ≤ oneMaximum N k mX mY) ∧
  (∀ (J : Encoder N mX mY) (sigma : PageStates mX),
    directContract N k mX mY J sigma →
    ∀ (b : Bool) (psi : Logical N → ℂ), purePage N b psi →
      encodedSchmidtRank J psi = pageRank sigma b) ∧
  (∀ (J : Encoder N mX mY) (sigma : PageStates mX),
    directContract N k mX mY J sigma →
      vonNeumannEntropy (sigma false) ≤ Real.log (zeroMaximum N k mX mY) ∧
      vonNeumannEntropy (sigma true) ≤ Real.log (oneMaximum N k mX mY)) ∧
  (1 ≤ zeroMaximum N k mX mY → 1 ≤ oneMaximum N k mX mY →
    ∃ (J : Encoder N mX mY) (sigma : PageStates mX),
      directContract N k mX mY J sigma ∧
      pageRank sigma false = zeroMaximum N k mX mY ∧
      pageRank sigma true = oneMaximum N k mX mY ∧
      vonNeumannEntropy (sigma false) = Real.log (zeroMaximum N k mX mY) ∧
      vonNeumannEntropy (sigma true) = Real.log (oneMaximum N k mX mY))

end D5.S3.Quantum.Entanglement.KBonacciDirectRankEntropy

namespace D5.S3.Quantum.Entanglement.KBonacciDirectRankEntropy
open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Information.InputInformationBalance
open D5.S3.Entropy.MaxEntropy
set_option maxRecDepth 2000
set_option maxHeartbeats 1600000 in
theorem complete_original_direct_rank_entropy : completeOriginal72 := by
  classical
  intro N k mX mY hN hk hmX hmY
  have hdim (b : Bool) : 0 < logicalDimension N b := by
    apply Finset.card_pos.mpr
    cases b with
    | false => exact ⟨⟨0,by omega⟩,by simp [primeNumbers,Nat.not_prime_zero]⟩
    | true => exact ⟨⟨2,by omega⟩,by simp [primeNumbers,Nat.prime_two]⟩
  have necessity (J : Encoder N mX mY) (sigma : PageStates mX)
      (hc : directContract N k mX mY J sigma) :
      pageRank sigma false ≤ zeroMaximum N k mX mY ∧
      pageRank sigma true ≤ oneMaximum N k mX mY ∧
      totalRowSpectralNecessity N k mX mY J sigma := by
    have h := D5.S3.Quantum.Entanglement.KBonacciDirectSupportObstruction.actual_encoder_spectral_obstruction
      N k mX mY hN hk hmX hmY J sigma hc
    rcases h false with ⟨_,_,_,_,_,_,h0⟩
    rcases h true with ⟨W,hW,hr,hs,hq,ht,h1⟩
    exact ⟨h0,h1,W,hW,hr,hs,hq,ht rfl⟩
  have selectOne (d : ℕ) (hd : d ≤ oneMaximum N k mX mY) :
    ∃ X : Fin d → Word mX, Function.Injective X ∧
      (∀ j, X j ∈ wordPages k mX true) ∧
      (∀ s, ((Finset.univ : Finset (Fin d)).filter (fun j => s ≤ terminalRun (X j))).card =
        d - earlierRows k mX s) ∧
      ∃ Y : PrimePage N true × Fin d → Word mY,
        Function.Injective Y ∧
        (∀ r j, Y (r,j) ∈ oneNeighborhood k mY (terminalRun (X j))) ∧
        (∀ r j, DBonacciAdmissible k (mX + mY) (Fin.append (X j) (Y (r,j)))) := by
    classical
    have hfold : ∀ (l : List ℕ) (a t : ℕ), t ≤ l.foldl min a ↔
        t ≤ a ∧ ∀ u ∈ l, t ≤ u := by
      intro l
      induction l with
      | nil => simp
      | cons v l ih => simp [List.foldl, ih, le_min_iff, and_assoc]
    have hb := (hfold _ _ d).mp hd
    have hdc : d ≤ capacity k mX true := hb.1
    have hds (s : ℕ) (hs : s < k) :
        d ≤ earlierRows k mX s + neighborCount k mY s / logicalDimension N true :=
      hb.2 _ (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩)
    let key : Word mX → ℕ ×ₗ Lex (Word mX) := fun w => toLex (terminalRun w, toLex w)
    have hkey : Function.Injective key := by
      intro x y h
      exact congrArg (fun z : ℕ ×ₗ Lex (Word mX) => ofLex (ofLex z).2) h
    let ord : LinearOrder (Word mX) := LinearOrder.lift' key hkey
    letI : LinearOrder (Word mX) := ord
    letI : Preorder (Word mX) := ord.toPreorder
    letI : LE (Word mX) := ord.toLE
    letI : LT (Word mX) := ord.toLT
    let e : Fin (capacity k mX true) ↪o Word mX := (wordPages k mX true).orderEmbOfFin rfl
    have hem (i : Fin (capacity k mX true)) : e i ∈ wordPages k mX true :=
      Finset.orderEmbOfFin_mem _ _ i
    have hmono : Monotone (fun i : Fin (capacity k mX true) => terminalRun (e i)) := by
      intro i j hij
      have h := e.monotone hij
      exact Prod.Lex.monotone_fst _ _ h
    have hlows (s : ℕ) : ((wordPages k mX true).filter (fun x => terminalRun x < s)).card =
        earlierRows k mX s := by
      dsimp [earlierRows, stateRows]
      simpa using (Finset.sum_card_fiberwise_eq_card_filter
        (s := wordPages k mX true) (t := Finset.range s) (g := terminalRun)).symm
    have hlowcard (s : ℕ) :
        ((Finset.univ : Finset (Fin (capacity k mX true))).filter
          (fun i => terminalRun (e i) < s)).card = earlierRows k mX s := by
      rw [← hlows s]
      apply Finset.card_bij (fun i _ => e i)
      · intro i hi
        exact Finset.mem_filter.mpr ⟨hem i, (Finset.mem_filter.mp hi).2⟩
      · intro i _ j _ h
        exact e.injective h
      · intro x hx
        have hxm := (Finset.mem_filter.mp hx).1
        obtain ⟨i, hi⟩ := (wordPages k mX true).orderIsoOfFin rfl |>.surjective ⟨x,hxm⟩
        refine ⟨i, ?_, congrArg Subtype.val hi⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ i, ?_⟩
        have hev : e i = x := congrArg Subtype.val hi
        rw [hev]
        exact (Finset.mem_filter.mp hx).2
    have hindex (s : ℕ) (i : Fin (capacity k mX true)) :
        terminalRun (e i) < s ↔ i.val < earlierRows k mX s := by
      constructor
      · intro hi
        have hsub : Finset.Iic i ⊆
            (Finset.univ : Finset (Fin (capacity k mX true))).filter
              (fun j => terminalRun (e j) < s) := by
          intro j hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (hmono (Finset.mem_Iic.mp hj)).trans_lt hi⟩
        have h := Finset.card_le_card hsub
        rw [hlowcard s] at h
        have h' : i.val + 1 ≤ earlierRows k mX s := by simpa only [Fin.card_Iic] using h
        omega
      · intro hi
        by_contra h
        have hsub : ((Finset.univ : Finset (Fin (capacity k mX true))).filter
            (fun j => terminalRun (e j) < s)) ⊆ Finset.Iio i := by
          intro j hj
          apply Finset.mem_Iio.mpr
          have hj' := (Finset.mem_filter.mp hj).2
          by_contra hn
          have hij : i ≤ j := le_of_not_gt hn
          exact h ((hmono hij).trans_lt hj')
        have h' := Finset.card_le_card hsub
        rw [hlowcard s, Fin.card_Iio] at h'
        omega
    let X : Fin d → Word mX := fun j => e (Fin.castLE hdc j)
    have hXinj : Function.Injective X := e.injective.comp (Fin.castLE_injective hdc)
    have hXm (j : Fin d) : X j ∈ wordPages k mX true := hem _
    have htail (s : ℕ) : ((Finset.univ : Finset (Fin d)).filter
        (fun j => s ≤ terminalRun (X j))).card = d - earlierRows k mX s := by
      have hpred (j : Fin d) : s ≤ terminalRun (X j) ↔ earlierRows k mX s ≤ j.val := by
        have h := hindex s (Fin.castLE hdc j)
        simp only [Fin.val_castLE] at h
        dsimp only [X]
        omega
      simp_rw [hpred]
      have hcomp : ((Finset.univ : Finset (Fin d)).filter
          (fun j => earlierRows k mX s ≤ j.val)) =
        (Finset.univ.filter (fun j : Fin d => j.val < earlierRows k mX s))ᶜ := by
        ext j; simp
      rw [hcomp, Finset.card_compl]
      have hlow : (Finset.univ.filter (fun j : Fin d => j.val < earlierRows k mX s)).card =
          min d (earlierRows k mX s) := by
        exact Fin.card_filter_val_lt
      rw [hlow, Fintype.card_fin]
      omega
    have join := actual_direct_concatenation k mX mY hk
    have hstate (j : Fin d) : terminalRun (X j) < k := by
      have hx := (Finset.mem_filter.mp (hXm j)).2.1
      exact ((actual_direct_concatenation k mX mX hk).1 (X j) (X j) hx hx).1
    have hbound (s : ℕ) (hs : s < k) :
        logicalDimension N true * (d - earlierRows k mX s) ≤ neighborCount k mY s := by
      have hle : d - earlierRows k mX s ≤ neighborCount k mY s / logicalDimension N true := by
        exact Nat.sub_le_iff_le_add.mpr (by simpa [Nat.add_comm] using hds s hs)
      exact (Nat.mul_le_mul_left _ hle).trans (Nat.mul_div_le _ _)
    let T : PrimePage N true × Fin d → Finset (Word mY) :=
      fun rj => oneNeighborhood k mY (terminalRun (X rj.2))
    have hHall (S : Finset (PrimePage N true × Fin d)) : S.card ≤ (S.biUnion T).card := by
      by_cases hn : S.Nonempty
      · let states := S.image (fun rj => terminalRun (X rj.2))
        have hsn : states.Nonempty := hn.image _
        let s := states.min' hsn
        have hsm : s ∈ states := Finset.min'_mem _ _
        obtain ⟨rj, hrj, hsj⟩ := Finset.mem_image.mp hsm
        have hs : s < k := by rw [← hsj]; exact hstate rj.2
        have hS : S ⊆ Finset.univ ×ˢ
            (Finset.univ.filter (fun j : Fin d => s ≤ terminalRun (X j))) := by
          intro ti hti
          simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and]
          exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨ti,hti,rfl⟩)
        have hunion : S.biUnion T = oneNeighborhood k mY s := by
          apply Finset.Subset.antisymm
          · intro y hy
            obtain ⟨ti, hti, hy⟩ := Finset.mem_biUnion.mp hy
            exact join.2.1 s (terminalRun (X ti.2))
              (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨ti,hti,rfl⟩)) hy
          · intro y hy
            exact Finset.mem_biUnion.mpr ⟨rj,hrj,by simpa [T,hsj] using hy⟩
        rw [hunion]
        calc
          S.card ≤ (Finset.univ ×ˢ
              (Finset.univ.filter (fun j : Fin d => s ≤ terminalRun (X j)))).card :=
            Finset.card_le_card hS
          _ = logicalDimension N true * (d - earlierRows k mX s) := by
            rw [Finset.card_product, htail, Finset.card_univ]
            simp [logicalDimension, PrimePage]
          _ ≤ (oneNeighborhood k mY s).card := hbound s hs
      · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        simp [hS]
    obtain ⟨Y, hYinj, hYm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' T).mp hHall
    refine ⟨X,hXinj,hXm,htail,Y,hYinj,fun r j => hYm (r,j),?_⟩
    intro r j
    have hx := (Finset.mem_filter.mp (hXm j)).2.1
    have hy := (Finset.mem_filter.mp (hYm (r,j))).2
    apply (join.1 (X j) (Y (r,j)) hx hy.1).2.2.mpr
    change terminalRun (X j) + initialRun (Y (r,j)) < k
    have hi : initialRun (Y (r,j)) < k - terminalRun (X j) := hy.2.2
    have hs := hstate j
    omega
  have selectZero (d : ℕ) (hd : d ≤ zeroMaximum N k mX mY) :
      ∃ X : Fin d → Word mX, Function.Injective X ∧ (∀ j, X j ∈ wordPages k mX false) ∧
      ∃ Y : PrimePage N false × Fin d → Word mY, Function.Injective Y ∧
        (∀ r j, Y (r,j) ∈ wordPages k mY false) ∧
        (∀ r j, DBonacciAdmissible k (mX + mY) (Fin.append (X j) (Y (r,j)))) := by
    have hdc : d ≤ capacity k mX false := hd.trans (Nat.min_le_left _ _)
    have hdy : logicalDimension N false * d ≤ capacity k mY false := by
      have hdiv : d ≤ capacity k mY false / logicalDimension N false := hd.trans (Nat.min_le_right _ _)
      exact (Nat.mul_le_mul_left _ hdiv).trans (Nat.mul_div_le _ _)
    let ex : Fin (capacity k mX false) ≃ ↥(wordPages k mX false) :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_coe, capacity])
    let ey : Fin (capacity k mY false) ≃ ↥(wordPages k mY false) :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_coe, capacity])
    let er : PrimePage N false × Fin d ≃ Fin (logicalDimension N false * d) :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, logicalDimension, PrimePage])
    let X : Fin d → Word mX := fun j => (ex (Fin.castLE hdc j)).val
    let Y : PrimePage N false × Fin d → Word mY := fun rj =>
      (ey (Fin.castLE hdy (er rj))).val
    have hXm (j : Fin d) : X j ∈ wordPages k mX false := (ex _).property
    have hYm (r : PrimePage N false) (j : Fin d) : Y (r,j) ∈ wordPages k mY false := (ey _).property
    refine ⟨X,?_,hXm,Y,?_,hYm,?_⟩
    · intro i j h;exact Fin.castLE_injective hdc (ex.injective (Subtype.ext h))
    · intro i j h;exact er.injective (Fin.castLE_injective hdy (ey.injective (Subtype.ext h)))
    · intro r j
      exact (actual_direct_concatenation k mX mY hk).2.2.2 (X j) (Y (r,j))
        (Finset.mem_filter.mp (hXm j)).2.1 (Finset.mem_filter.mp (hYm r j)).2.1
        (Finset.mem_filter.mp (hYm r j)).2.2
  have construction (d0 d1 : ℕ) (hd0 : 1 ≤ d0) (hd0max : d0 ≤ zeroMaximum N k mX mY)
      (hd1 : 1 ≤ d1) (hd1max : d1 ≤ oneMaximum N k mX mY) :
      ∃ (J : Encoder N mX mY) (sigma : PageStates mX), directContract N k mX mY J sigma ∧
        pageRank sigma false = d0 ∧ pageRank sigma true = d1 ∧
        vonNeumannEntropy (sigma false) = Real.log d0 ∧
        vonNeumannEntropy (sigma true) = Real.log d1 := by
    obtain ⟨X0,hX0,hXm0,Y0,hY0,hYm0,hlegal0⟩ := selectZero d0 hd0max
    obtain ⟨X1,hX1,hXm1,_hcount1,Y1,hY1,hYm1,hlegal1⟩ := selectOne d1 hd1max
    let d : Bool → ℕ := fun b => if b then d1 else d0
    have hd (b : Bool) : 0 < d b := by cases b <;> simp [d] <;> omega
    let X : ∀ b, Fin (d b) → Word mX := fun b => match b with
      | false => X0
      | true => X1
    have hX (b : Bool) : Function.Injective (X b) := by cases b;exact hX0;exact hX1
    have hXm (b : Bool) (j : Fin (d b)) : X b j ∈ wordPages k mX b := by
      cases b;exact hXm0 j;exact hXm1 j
    let Y : (Σ b : Bool, PrimePage N b × Fin (d b)) → Word mY := fun t => match t with
      | ⟨false,rj⟩ => Y0 rj
      | ⟨true,rj⟩ => Y1 rj
    have hYm (t : Σ b : Bool, PrimePage N b × Fin (d b)) : Y t ∈ wordPages k mY t.1 := by
      rcases t with ⟨b,r,j⟩
      cases b;exact hYm0 r j
      · have h := (Finset.mem_filter.mp (hYm1 r j)).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,h.2.1⟩
    have hY : Function.Injective Y := by
      rintro ⟨b,rj⟩ ⟨c,si⟩ h
      cases b <;> cases c
      · exact congrArg (fun t => (⟨false,t⟩ : Σ b : Bool, PrimePage N b × Fin (d b))) (hY0 h)
      · have h0 := (Finset.mem_filter.mp (hYm ⟨false,rj⟩)).2.2
        have h1 := (Finset.mem_filter.mp (hYm ⟨true,si⟩)).2.2
        rw [h] at h0
        rw [h1] at h0
        simp at h0
      · have h1 := (Finset.mem_filter.mp (hYm ⟨true,rj⟩)).2.2
        have h0 := (Finset.mem_filter.mp (hYm ⟨false,si⟩)).2.2
        rw [h] at h1
        rw [h0] at h1
        simp at h1
      · exact congrArg (fun t => (⟨true,t⟩ : Σ b : Bool, PrimePage N b × Fin (d b))) (hY1 h)
    have hlegal (t : Σ b : Bool, PrimePage N b × Fin (d b)) :
        DBonacciAdmissible k (mX + mY) (Fin.append (X t.1 t.2.2) (Y t)) := by
      rcases t with ⟨b,r,j⟩
      cases b;exact hlegal0 r j;exact hlegal1 r j
    have assembled : ∃ (J : Encoder N mX mY) (sigma : PageStates mX),
        directContract N k mX mY J sigma ∧
        (∀ b, pageRank sigma b = d b) ∧
        (∀ b, vonNeumannEntropy (sigma b) = Real.log (d b)) := by
      classical
      let T := Σ b : Bool, PrimePage N b × Fin (d b)
      let p : T → Word mX × Word mY := fun t => (X t.1 t.2.2, Y t)
      let l : T → Logical N := fun t => ⟨t.1,t.2.1⟩
      let a : Bool → ℂ := fun b => (Real.sqrt (d b : ℝ))⁻¹
      have hdn (b : Bool) : (d b : ℝ) ≠ 0 := by exact_mod_cast (hd b).ne'
      have ha (b : Bool) : star (a b) = a b := by simp [a]
      have haa (b : Bool) : a b * a b = (d b : ℂ)⁻¹ := by
        have hsq : (Real.sqrt (d b : ℝ))^2 = (d b : ℝ) := Real.sq_sqrt (by positivity)
        calc
          a b * a b = ((Real.sqrt (d b : ℝ) : ℂ)^2)⁻¹ := by dsimp [a];ring
          _ = (d b : ℂ)⁻¹ := by congr 1;exact_mod_cast hsq
      let J : Encoder N mX mY := ∑ t : T, Matrix.single (p t) (l t) (a t.1)
      let prob (b : Bool) : Fin (d b) → ℝ := fun _ => (d b : ℝ)⁻¹
      have hp (b : Bool) : ∀ j, 0 ≤ prob b j := by intro j; dsimp [prob]; positivity
      have hps (b : Bool) : ∑ j, prob b j = 1 := by simp [prob,hdn b]
      let sigma : PageStates mX := fun b => mixtureState (prob b) (hp b) (hps b)
        (fun j => pointerState (X b j))
      have hsig (b : Bool) : CStarMatrix.ofMatrix.symm (sigma b).val =
          ∑ j : Fin (d b), Matrix.single (X b j) (X b j) (d b : ℂ)⁻¹ := by
        ext x z
        change (CStarMatrix.ofMatrixStarAlgEquiv.symm (∑ j : Fin (d b),
          (d b : ℝ)⁻¹ • (pointerState (X b j)).val)) x z = _
        rw [map_sum]
        simp only [Matrix.sum_apply]
        apply Finset.sum_congr rfl
        intro j _
        change ((d b : ℝ)⁻¹ • Matrix.diagonal (fun w : Word mX =>
          if w = X b j then (1 : ℂ) else 0)) x z = _
        by_cases hxz : x = z
        · subst z
          by_cases hx : X b j = x <;> simp [Matrix.smul_apply,Matrix.diagonal_apply,
            Matrix.single_apply,hx,Ne.symm,eq_comm,Complex.real_smul]
        · have hn : ¬(X b j = x ∧ X b j = z) := by rintro ⟨h1,h2⟩;exact hxz (h1.symm.trans h2)
          simp [Matrix.smul_apply,Matrix.diagonal_apply,Matrix.single_apply,hxz,hn]
      have hJ (x : Word mX) (y : Word mY) (q : Logical N) :
          J (x,y) q = ∑ t : T, if (X t.1 t.2.2 = x ∧ Y t = y ∧ l t = q) then a t.1 else 0 := by
        simp only [J, Matrix.sum_apply, Matrix.single_apply, p, Prod.mk.injEq]
        apply Finset.sum_congr rfl
        intro t _
        simp only [and_assoc]
      have hrow (q v : Logical N) (x z : Word mX) :
          (∑ y : Word mY, J (x,y) q * star (J (z,y) v)) =
            ∑ t : T, if (l t = q ∧ l t = v ∧ X t.1 t.2.2 = x ∧ X t.1 t.2.2 = z)
              then (d t.1 : ℂ)⁻¹ else 0 := by
        have hstar (u : T) (y : Word mY) :
            star (if X u.1 u.2.2 = z ∧ Y u = y ∧ l u = v then a u.1 else 0) =
              if X u.1 u.2.2 = z ∧ Y u = y ∧ l u = v then a u.1 else 0 := by
          split_ifs <;> simp [ha]
        simp_rw [hJ, star_sum, hstar, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_comm]
        have hcollapse (u : T) :
          (∑ y : Word mY,
            (if X t.1 t.2.2 = x ∧ Y t = y ∧ l t = q then a t.1 else 0) *
            (if X u.1 u.2.2 = z ∧ Y u = y ∧ l u = v then a u.1 else 0)) =
            if (t = u ∧ l t = q ∧ l u = v ∧ X t.1 t.2.2 = x ∧ X u.1 u.2.2 = z)
              then a t.1 * a u.1 else 0 := by
          by_cases hx : X t.1 t.2.2 = x
          · by_cases hz : X u.1 u.2.2 = z
            · by_cases hl : l t = q
              · by_cases hv : l u = v
                · simp only [hx,hz,hl,hv,true_and,and_true]
                  by_cases htu : t = u
                  · subst u; simp
                  · have hne : Y t ≠ Y u := fun h => htu (hY h)
                    simp [htu,hne,eq_comm]
                · simp [hv]
              · simp [hl]
            · simp [hz]
          · simp [hx]
        simp_rw [hcollapse]
        rw [Finset.sum_eq_single t]
        · simp [haa]
        · intro u _ hut
          simp [Ne.symm hut]
        · simp
      have hunit (q v : Logical N) :
          partialTraceRight (J * Matrix.single q v (1 : ℂ) * J.conjTranspose) =
            if q = v then CStarMatrix.ofMatrix.symm (sigma q.1).val else 0 := by
        ext x z
        change (∑ y, (J * Matrix.single q v (1 : ℂ) * J.conjTranspose) (x,y) (z,y)) = _
        simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply]
        simp only [ite_and, mul_ite, ite_mul, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, zero_mul, Finset.sum_ite_eq]
        rw [hrow]
        rcases q with ⟨b,r⟩
        rcases v with ⟨c,s⟩
        by_cases he : (⟨b,r⟩ : Logical N) = ⟨c,s⟩
        · cases he
          simp only [ite_true, hsig, Matrix.sum_apply, Matrix.single_apply]
          rw [Fintype.sum_sigma]
          simp [l, Fintype.sum_prod_type, Sigma.mk.inj_iff, Prod.mk.injEq, eq_comm, ite_and]
        · have hnil (t : T) : ¬ (l t = ⟨b,r⟩ ∧ l t = ⟨c,s⟩ ∧
              X t.1 t.2.2 = x ∧ X t.1 t.2.2 = z) := by
            rintro ⟨h1,h2,_⟩; exact he (h1.symm.trans h2)
          simp [he,hnil]
      have hiso : J.conjTranspose * J = 1 := by
        ext q v
        have h := congrArg Matrix.trace (hunit v q)
        have ht (b : Bool) : Matrix.trace (CStarMatrix.ofMatrix.symm (sigma b).val) = 1 :=
          (sigma b).property.2
        change Matrix.trace (partialTraceRight (J * Matrix.single v q (1 : ℂ) * J.conjTranspose)) =
          Matrix.trace (if v = q then CStarMatrix.ofMatrix.symm (sigma v.1).val else 0) at h
        rw [apply_ite Matrix.trace] at h
        simp only [ht,Matrix.trace_zero] at h
        simp only [Matrix.trace, partialTraceRight] at h
        change (∑ w : Word mX × Word mY, star (J w q) * J w v) = if q = v then 1 else 0
        rw [Fintype.sum_prod_type]
        simpa [partialTraceRight,Matrix.trace,Matrix.mul_apply,Matrix.single_apply,
          Matrix.conjTranspose_apply,ite_and,mul_ite,ite_mul,eq_comm,mul_comm] using h
      refine ⟨J,sigma,?_,?_,?_⟩
      · refine ⟨hiso,?_,?_,?_⟩
        · intro b
          have hcol (q : Logical N) (x : Word mX) (y : Word mY) :
              (x ∈ wordPages k mX b ↔ q.1 = b) ∨ J (x,y) q = 0 := by
            by_cases hx : x ∈ wordPages k mX q.1
            · have hb : x ∈ wordPages k mX b ↔ q.1 = b := by
                have hhead := (Finset.mem_filter.mp hx).2.2
                simp only [wordPages,Finset.mem_filter,Finset.mem_univ,true_and]
                constructor
                · intro h; exact Option.some.inj (hhead.symm.trans h.2)
                · intro h; simpa [h] using (Finset.mem_filter.mp hx).2
              exact Or.inl hb
            · right
              rw [hJ]
              apply Finset.sum_eq_zero
              intro t _
              split_ifs with h
              · have hl : t.1 = q.1 := congrArg Sigma.fst h.2.2
                exact False.elim (hx (by rw [← h.1,← hl];exact hXm _ _))
              · rfl
          have hcolY (q : Logical N) (x : Word mX) (y : Word mY) :
              (y ∈ wordPages k mY b ↔ q.1 = b) ∨ J (x,y) q = 0 := by
            by_cases hy : y ∈ wordPages k mY q.1
            · have hhead := (Finset.mem_filter.mp hy).2.2
              left
              simp only [wordPages,Finset.mem_filter,Finset.mem_univ,true_and]
              constructor
              · intro h; exact Option.some.inj (hhead.symm.trans h.2)
              · intro h; simpa [h] using (Finset.mem_filter.mp hy).2
            · right
              rw [hJ]
              apply Finset.sum_eq_zero
              intro t _
              split_ifs with h
              · have hl : t.1 = q.1 := congrArg Sigma.fst h.2.2
                exact False.elim (hy (by rw [← h.2.1,← hl];exact hYm t))
              · rfl
          refine ⟨?_,?_,?_⟩
          · ext xy q
            rcases xy with ⟨x,y⟩
            simp [physicalProjection,logicalProjection,Matrix.mul_apply,Matrix.diagonal_apply,
              Matrix.kronecker_apply,Matrix.one_apply,Fintype.sum_prod_type]
            rcases hcol q x y with h | h
            · simp [h]
            · simp [h]
          · ext xy q
            rcases xy with ⟨x,y⟩
            simp [physicalProjection,logicalProjection,Matrix.mul_apply,Matrix.diagonal_apply,
              Matrix.kronecker_apply,Matrix.one_apply,Fintype.sum_prod_type]
            rcases hcolY q x y with h | h
            · simp [h]
            · simp [h]
          · rw [hsig]
            ext x z
            simp only [Matrix.mul_apply,physicalProjection,Matrix.diagonal_apply,Matrix.sum_apply]
            simp only [ite_and,mul_ite,ite_mul,one_mul,mul_one,mul_zero,zero_mul,
              Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_ite_eq]
            have hzero : ∀ (j : Fin (d b)),
                (if z ∈ wordPages k mX b then
                  if x ∈ wordPages k mX b then Matrix.single (X b j) (X b j) (d b : ℂ)⁻¹ x z else 0
                else 0) = Matrix.single (X b j) (X b j) (d b : ℂ)⁻¹ x z := by
              intro j
              by_cases hx : X b j = x
              · by_cases hz : X b j = z
                · subst x;subst z;simp [hXm]
                · simp [Matrix.single_apply,hz]
              · simp [Matrix.single_apply,hx]
            have h : (∑ j : Fin (d b), if z ∈ wordPages k mX b then
                if x ∈ wordPages k mX b then Matrix.single (X b j) (X b j) (d b : ℂ)⁻¹ x z else 0
                else 0) = ∑ j : Fin (d b), Matrix.single (X b j) (X b j) (d b : ℂ)⁻¹ x z :=
              Finset.sum_congr rfl (fun j _ => hzero j)
            simpa only [Finset.sum_ite_irrel,Finset.sum_const_zero] using h
        · intro A
          ext x z
          simp only [partialTraceRight,Matrix.mul_apply,Matrix.conjTranspose_apply]
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          have hexchange : (∑ v : Logical N, ∑ y : Word mY, ∑ q : Logical N,
              J (x,y) q * A q v * star (J (z,y) v)) =
            ∑ v : Logical N, ∑ q : Logical N, A q v *
              (∑ y : Word mY, J (x,y) q * star (J (z,y) v)) := by
            apply Finset.sum_congr rfl
            intro v _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro q _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
          rw [hexchange]
          have hentry (q v : Logical N) : (∑ y : Word mY, J (x,y) q * star (J (z,y) v)) =
            if q = v then (CStarMatrix.ofMatrix.symm (sigma q.1).val) x z else 0 := by
            have h := congrArg (fun M : Matrix (Word mX) (Word mX) ℂ => M x z) (hunit q v)
            simpa [partialTraceRight,Matrix.mul_apply,Matrix.single_apply,Matrix.conjTranspose_apply,
              ite_and,mul_ite,ite_mul,Matrix.ite_apply,Matrix.zero_apply] using h
          simp_rw [hentry]
          simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true,
            Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
          rw [Fintype.sum_sigma]
          simp [logicalProjection,Matrix.trace,Matrix.mul_apply,Matrix.diagonal_apply,
            Fintype.sum_sigma,Finset.mul_sum,Finset.sum_mul]
        · intro psi x y hn
          rw [Matrix.mulVec, dotProduct]
          apply Finset.sum_eq_zero
          intro q _
          have hz : J (x,y) q = 0 := by
            rw [hJ]
            apply Finset.sum_eq_zero
            intro t _
            split_ifs with h
            · exact False.elim (hn (by rw [← h.1,← h.2.1];exact hlegal t))
            · rfl
          simp [hz]
      · intro b
        have hdiag : CStarMatrix.ofMatrix.symm (sigma b).val =
            Matrix.diagonal (fun x => if x ∈ Finset.univ.image (X b) then (d b : ℂ)⁻¹ else 0) := by
          rw [hsig]
          ext x z
          simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply]
          by_cases hxz : x = z
          · subst z
            by_cases hx : x ∈ Finset.univ.image (X b)
            · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
              simp [hX b |>.eq_iff,eq_comm]
            · have hn (j : Fin (d b)) : X b j ≠ x := by
                intro h; exact hx (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,h⟩)
              simp [hx,hn]
          · have hn (j : Fin (d b)) : ¬ (X b j = x ∧ X b j = z) := by
              rintro ⟨h1,h2⟩;exact hxz (h1.symm.trans h2)
            simp [hxz,hn]
        rw [pageRank,hdiag,Matrix.rank_diagonal]
        have heq : {x : Word mX // (if x ∈ Finset.univ.image (X b) then (d b : ℂ)⁻¹ else 0) ≠ 0} ≃ Fin (d b) :=
          (Equiv.ofBijective (fun j : Fin (d b) =>
            (⟨X b j, by simp [hd b |>.ne']⟩ : {x : Word mX //
              (if x ∈ Finset.univ.image (X b) then (d b : ℂ)⁻¹ else 0) ≠ 0}))
            ⟨fun i j h => hX b (congrArg Subtype.val h), by
              intro x
              have hx : x.val ∈ Finset.univ.image (X b) := by
                by_contra hn;simpa [hn] using x.property
              obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hx
              exact ⟨j,Subtype.ext hj⟩⟩).symm
        exact (Fintype.card_congr heq).trans (Fintype.card_fin _)
      · intro b
        have ho : Pairwise (fun i j : Fin (d b) =>
            (pointerState (X b i)).val * (pointerState (X b j)).val = 0) := by
          intro i j hij
          have hx : X b i ≠ X b j := fun h => hij (hX b h)
          exact pointerState_orthogonal hx
        rw [orthogonal_mixture_entropy (prob b) (hp b) (hps b) (fun j => pointerState (X b j)) ho]
        simp only [entropy_pointerState,mul_zero,Finset.sum_const_zero,add_zero]
        simp [shannonEntropy,prob,Real.negMulLog,Real.log_inv,hdn b]
    obtain ⟨J,sigma,hc,hr,he⟩ := assembled
    exact ⟨J,sigma,hc,hr false,hr true,he false,he true⟩
  have rankEntropy (rho : DensityState (Word mX)) :
      0 < Matrix.rank (CStarMatrix.ofMatrix.symm rho.val) ∧
      vonNeumannEntropy rho ≤ Real.log (Matrix.rank (CStarMatrix.ofMatrix.symm rho.val)) := by
    classical
    let hPos : (CStarMatrix.ofMatrix.symm rho.val).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.property.1)
    let lam := hPos.isHermitian.eigenvalues
    let D := {j : Word mX // lam j ≠ 0}
    have hsum : ∑ j : Word mX, lam j = 1 := by
      have ht := hPos.isHermitian.trace_eq_sum_eigenvalues
      have htr : Matrix.trace (CStarMatrix.ofMatrix.symm rho.val) = 1 := rho.property.2
      rw [htr] at ht
      simpa [lam] using congrArg Complex.re ht.symm
    have hex : ∃ j : Word mX, lam j ≠ 0 := by
      by_contra hn
      push Not at hn
      have hz : ∑ j : Word mX, lam j = 0 := by simp [hn]
      rw [hz] at hsum
      norm_num at hsum
    letI : Nonempty D := by obtain ⟨j,hj⟩ := hex;exact ⟨⟨j,hj⟩⟩
    have hc : Fintype.card D = Matrix.rank (CStarMatrix.ofMatrix.symm rho.val) := by
      exact hPos.isHermitian.rank_eq_card_non_zero_eigs.symm
    have hs : ∑ j : D, lam j.val = 1 := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun j => lam j ≠ 0)) (by simp) lam]
      rw [Finset.sum_filter]
      have hzero (j : Word mX) : (if lam j ≠ 0 then lam j else 0) = lam j := by
        split_ifs with hj
        · rfl
        · exact (not_ne_iff.mp hj).symm
      simpa only [hzero] using hsum
    have he : vonNeumannEntropy rho = shannonEntropy (fun j : D => lam j.val) := by
      rw [entropy_eq_sum,shannonEntropy]
      change (∑ j : Word mX, Real.negMulLog (lam j)) = _
      rw [← Finset.sum_subtype (Finset.univ.filter (fun j => lam j ≠ 0)) (by simp)
        (fun j => Real.negMulLog (lam j))]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : lam j ≠ 0
      · simp [hj]
      · simp [not_ne_iff.mp hj]
    refine ⟨?_,?_⟩
    · rw [← hc];exact Fintype.card_pos
    · rw [he,← hc]
      exact entropy_le_log_card (fun j : D => lam j.val) ⟨fun j => hPos.eigenvalues_nonneg j.val,hs⟩
  refine ⟨hdim false,hdim true,necessity,?_,?_,?_,?_,?_⟩
  · intro d0 d1
    constructor
    · rintro ⟨J,sigma,hc,hr0,hr1⟩
      have hn := necessity J sigma hc
      have hp0 := (rankEntropy (sigma false)).1
      have hp1 := (rankEntropy (sigma true)).1
      change 0 < pageRank sigma false at hp0
      change 0 < pageRank sigma true at hp1
      rw [hr0] at hp0
      rw [hr1] at hp1
      exact ⟨hp0,hr0 ▸ hn.1,hp1,hr1 ▸ hn.2.1⟩
    · rintro ⟨hd0,hm0,hd1,hm1⟩
      obtain ⟨J,sigma,hc,hr0,hr1,_⟩ := construction d0 d1 hd0 hm0 hd1 hm1
      exact ⟨J,sigma,hc,hr0,hr1⟩
  · constructor
    · rintro ⟨J,sigma,hc⟩
      have hn := necessity J sigma hc
      exact ⟨(rankEntropy (sigma false)).1.trans_le hn.1,
        (rankEntropy (sigma true)).1.trans_le hn.2.1⟩
    · rintro ⟨hm0,hm1⟩
      obtain ⟨J,sigma,hc,_⟩ := construction _ _ hm0 le_rfl hm1 le_rfl
      exact ⟨J,sigma,hc⟩
  · intro J sigma hc b psi hp
    classical
    let A := Matrix.vecMulVec psi (star psi)
    have ht (c : Bool) : Matrix.trace (logicalProjection N c * A) = if c = b then 1 else 0 := by
      simp only [logicalProjection,Matrix.diagonal_mul,Matrix.trace,Matrix.diag_apply,A,
        Matrix.vecMulVec_apply,Pi.star_apply]
      by_cases hcb : c = b
      · subst c
        rw [if_pos rfl]
        have hterm (l : Logical N) : (if l.1 = b then 1 else 0) * (psi l * star (psi l)) =
            star (psi l) * psi l := by
          by_cases hl : l.1 = b
          · simp [hl,mul_comm]
          · simp [hl,hp.2 l hl]
        simp_rw [hterm]
        exact hp.1
      · rw [if_neg hcb]
        apply Finset.sum_eq_zero
        intro l _
        by_cases hl : l.1 = c
        · have hlb : l.1 ≠ b := by simpa [hl] using hcb
          simp [hp.2 l hlb]
        · simp [hl]
    have hm := hc.2.2.1 A
    simp_rw [ht] at hm
    simp only [ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,if_true] at hm
    have hm' : partialTraceRight (J * A * J.conjTranspose) =
        CStarMatrix.ofMatrix.symm (sigma b).val := by
      cases b <;> simpa only [Fintype.sum_bool, Bool.false_eq_true, Bool.true_eq_false,
        if_false, if_true, add_zero, zero_add] using hm
    let v := Matrix.mulVec J psi
    let P : Matrix (Word mX) (Word mY) ℂ := fun x y => v (x,y)
    have hg : P * P.conjTranspose = CStarMatrix.ofMatrix.symm (sigma b).val := by
      rw [← hm']
      rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,Matrix.vecMul_conjTranspose]
      simp only [star_star]
      ext x z
      change (∑ y, v (x,y) * star (v (z,y))) = _
      rfl
    change P.rank = Matrix.rank (CStarMatrix.ofMatrix.symm (sigma b).val)
    rw [← hg,Matrix.rank_self_mul_conjTranspose]
  · intro J sigma hc
    have hn := necessity J sigma hc
    have hlog (b : Bool) (bound : ℕ) (hb : pageRank sigma b ≤ bound) :
        vonNeumannEntropy (sigma b) ≤ Real.log bound := by
      have hr := rankEntropy (sigma b)
      apply hr.2.trans
      apply Real.strictMonoOn_log.monotoneOn
      · change (0 : ℝ) < _
        exact_mod_cast hr.1
      · change (0 : ℝ) < _
        exact_mod_cast hr.1.trans_le hb
      · exact_mod_cast hb
    exact ⟨hlog false _ hn.1,hlog true _ hn.2.1⟩
  · intro hm0 hm1
    exact construction _ _ hm0 le_rfl hm1 le_rfl
#print axioms complete_original_direct_rank_entropy
end D5.S3.Quantum.Entanglement.KBonacciDirectRankEntropy
