/- GID: D5/S3/Combinatorics/Graph/Walks/CubicPowerClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CubicPowerClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Circulant, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: The complete native cubic-circulant classification and all positive-power spectra. -/
import D5.S3.Combinatorics.Graph.Walks.CubicCirculant
import D5.S3.Combinatorics.Graph.Walks.MobiusMetric
import D5.S3.Combinatorics.Graph.Walks.PentagonalPrismSquare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CubicCirculant
open SimpleGraph Finset
open WellCoveredPowerCliqueProduct (IsMaximalIndep WellCovered WCP power)
open MatchingCliqueCycle (spectrum)
open FiniteDistancePower
open D5.S3.Combinatorics.Graph.ZeroForcing.GridPowerZeroForcingRefutation (graphPower)
noncomputable section

/-- Native Cartesian prism, with at least three base vertices. -/
abbrev prism (r : ℕ) := (cycleGraph (r+3)) □ (⊤ : SimpleGraph (ZMod 2))

theorem prism_connected (r : ℕ) : (prism r).Connected :=
  connected_cycleGraph_add_one.boxProd connected_top

/-- Exact diameters follow from the existing cycle and Cartesian-product suppliers. -/
theorem prism_diameter (r : ℕ) : (prism r).diam = (r+3)/2+1 := by
  rw [WellCoveredPowerCliqueProduct.diam_cliqueProduct connected_cycleGraph_add_one (by omega : 2 ≤ 2),
    MatchingCliqueCycle.base_diameter]

private theorem connected_power_one {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hc : G.Connected) : power G 1 = G := by
  rw [← power_eq_connected hc, power_one]

private theorem wellCovered_iso {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : WellCovered G ↔ WellCovered H := by
  rw [wellCovered_iff_spectrum,wellCovered_iff_spectrum,spectrum_iso e]

private theorem connected_power_spectrum_iso {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    (hc : G.Connected) (e : G ≃g H) (d : ℕ) : spectrum (power G d) = spectrum (power H d) := by
  rw [← power_eq_connected hc,← power_eq_connected (e.connected_iff.mp hc)]
  exact spectrum_iso (powerIso e d)

/-- The native Möbius first-power classification includes all ladder sizes. -/
theorem mobius_wellCovered_iff (m : ℕ) : WellCovered (mobius m) ↔ m ≤ 2 := by
  rw [← wellCovered_iso (mobiusIso m)]
  exact BinaryRungSpectrum.twisted_wellCovered_iff

/-- The first-power spectrum of every well-covered prism is attained and uniform. -/
private theorem prism_small_spectrum (r : ℕ) (hr : r=0 ∨ r=2) :
    spectrum (prism r) = {r+2} := by
  ext k
  rw [BinaryRungSpectrum.prism_spectrum]
  simp only [Set.mem_singleton_iff,Nat.even_iff]
  rcases hr with rfl | rfl <;> omega

private theorem mobius_small_spectrum (m : ℕ) (hm : m ≤ 2) :
    spectrum (mobius m) = {if m=0 then 1 else 3} := by
  ext k
  rw [mobius_spectrum]
  simp only [Set.mem_singleton_iff,Nat.odd_iff]
  split_ifs <;> omega

/-- Uniform sizes at every positive prism power; the middle pentagonal case is structural. -/
def prismPowerSize (r d : ℕ) : ℕ :=
  if d=1 then r+2 else if r=2 ∧ d=2 then 2 else 1

/-- Uniform sizes at every positive Möbius power in the well-covered range. -/
def mobiusPowerSize (m d : ℕ) : ℕ :=
  if d=1 then (if m=0 then 1 else 3) else 1

/-- Every positive power of each admissible prism has its exact attained native spectrum. -/
theorem prism_power_spectrum (r : ℕ) (hr : r=0 ∨ r=2) (d : ℕ) (hd : 1 ≤ d) :
    spectrum (power (prism r) d) = {prismPowerSize r d} := by
  by_cases hd1 : d=1
  · subst d
    rw [connected_power_one (prism_connected r),prism_small_spectrum r hr]
    simp [prismPowerSize]
  · by_cases hmiddle : r=2 ∧ d=2
    · rcases hmiddle with ⟨rfl,rfl⟩
      have hsquare : spectrum (power (prism 2) 2) = {2} := by
        have hn : ∀ u : Fin 10, ∃ v, (cycleGraph 10).Adj u v := by
          intro u
          exact ⟨u+1,by simp [cycleGraph_adj]⟩
        have ht : ∀ u v w : Fin 10, (cycleGraph 10).Adj u v →
            (cycleGraph 10).Adj v w → (cycleGraph 10).Adj w u → False := by
          intro u v w huv hvw hwu
          have hu := u.isLt
          have hv := v.isLt
          have hw := w.isLt
          simp only [cycleGraph_adj,sub_eq_iff_eq_add',Fin.ext_iff,Fin.val_add,Fin.val_one] at huv hvw hwu
          omega
        have hs := FiniteDistancePower.spectrum_complement_triangleFree (G := cycleGraph 10) hn ht
        have e := FiniteDistancePower.complementIso pentagon_square_complement_iso
        have he := FiniteDistancePower.spectrum_iso e
        simpa only [compl_compl] using he.symm.trans hs
      simpa [prismPowerSize] using hsquare
    · have hdiam : (prism r).diam ≤ d := by
        rw [prism_diameter]
        rcases hr with rfl | rfl <;> omega
      rw [power_eq_top_of_diam_le (prism_connected r) hdiam,spectrum_top]
      simp [prismPowerSize,hd1,hmiddle]

/-- Every positive power of each admissible Möbius ladder has its exact attained spectrum. -/
theorem mobius_power_spectrum (m : ℕ) (hm : m ≤ 2) (d : ℕ) (hd : 1 ≤ d) :
    spectrum (power (mobius m) d) = {mobiusPowerSize m d} := by
  by_cases hd1 : d=1
  · subst d
    rw [connected_power_one (mobius_connected m),mobius_small_spectrum m hm]
    simp [mobiusPowerSize]
  · have hdiam : (mobius m).diam ≤ d := by rw [mobius_diameter]; omega
    rw [power_eq_top_of_diam_le (mobius_connected m) hdiam,spectrum_top]
    simp [mobiusPowerSize,hd1]

/-- The connected component size table at all positive powers. -/
def componentPowerSize (ell d : ℕ) : ℕ :=
  if d=1 then
    if ell=4 then 1 else if ell=3 then 2 else if ell=5 then 4 else 3
  else if ell=5 ∧ d=2 then 2 else 1

/-- First-power well-coveredness for the entire cubic range is the known five-order classification. -/
theorem first_wellCovered_iff (n a : ℕ) (hn : 4 ≤ n) (hne : Even n)
    (ha : 1 ≤ a) (halt : a < n/2) :
    WellCovered (cubic n a) ↔ n / Nat.gcd n a ∈ ({3,4,5,6,8} : Set ℕ) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  have hw : WellCovered (cubic n a) ↔
      ∀ C : (cubic n a).ConnectedComponent, WellCovered C.toSimpleGraph := by
    constructor
    · intro h C
      have hp : WellCovered (graphPower (cubic n a) 1) := by simpa only [power_one] using h
      have hh := (wellCovered_power_components 1).mp hp C
      simpa only [connected_power_one C.connected_toSimpleGraph] using hh
    · intro h
      have hp : WellCovered (graphPower (cubic n a) 1) :=
        (wellCovered_power_components 1).mpr (fun C => by
          simpa only [connected_power_one C.connected_toSimpleGraph] using h C)
      simpa only [power_one] using hp
  rw [hw]
  obtain ⟨_,he,ho⟩ := component_decomposition n a hn hne ha halt
  rcases Nat.even_or_odd (n / Nat.gcd n a) with hp | hp
  · obtain ⟨_,m,hell,he⟩ := he hp
    have hh : (∀ C : (cubic n a).ConnectedComponent, WellCovered C.toSimpleGraph) ↔ m ≤ 2 := by
      constructor
      · intro h
        let C := (cubic n a).connectedComponentMk (0 : ZMod n)
        obtain ⟨e⟩ := he C
        exact (mobius_wellCovered_iff m).mp ((wellCovered_iso e).mpr (h C))
      · intro hm C
        obtain ⟨e⟩ := he C
        exact (wellCovered_iso e).mp ((mobius_wellCovered_iff m).mpr hm)
    rw [hh,hell]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    omega
  · obtain ⟨_,_,r,hell,he⟩ := ho hp
    have hh : (∀ C : (cubic n a).ConnectedComponent, WellCovered C.toSimpleGraph) ↔ r=0 ∨ r=2 := by
      constructor
      · intro h
        let C := (cubic n a).connectedComponentMk (0 : ZMod n)
        obtain ⟨e⟩ := he C
        exact (BinaryRungSpectrum.prism_wellCovered_iff r).mp ((wellCovered_iso e).mpr (h C))
      · intro hr C
        obtain ⟨e⟩ := he C
        exact (wellCovered_iso e).mp ((BinaryRungSpectrum.prism_wellCovered_iff r).mpr hr)
    rw [hh,hell]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Nat.odd_iff] at hp ⊢
    omega

/-- Every actual component has the stated attained spectrum at every positive power. -/
theorem component_power_spectrum (n a : ℕ) (hn : 4 ≤ n) (hne : Even n)
    (ha : 1 ≤ a) (halt : a < n/2)
    (hclass : n / Nat.gcd n a ∈ ({3,4,5,6,8} : Set ℕ)) (d : ℕ) (hd : 1 ≤ d)
    (C : (cubic n a).ConnectedComponent) [Fintype C] :
    letI : NeZero n := ⟨by omega⟩
    spectrum (power C.toSimpleGraph d) = {componentPowerSize (n / Nat.gcd n a) d} := by
  classical
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨_,he,ho⟩ := component_decomposition n a hn hne ha halt
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hclass
  rcases Nat.even_or_odd (n / Nat.gcd n a) with hp | hp
  · obtain ⟨_,m,hell,he⟩ := he hp
    have hm : m ≤ 2 := by omega
    obtain ⟨e⟩ := he C
    rw [← connected_power_spectrum_iso (mobius_connected m) e,
      mobius_power_spectrum m hm d hd,hell]
    congr 1
    simp only [componentPowerSize,mobiusPowerSize]
    split_ifs <;> omega
  · obtain ⟨_,_,r,hell,he⟩ := ho hp
    have hr : r=0 ∨ r=2 := by
      simp only [Nat.odd_iff] at hp
      omega
    obtain ⟨e⟩ := he C
    rw [← connected_power_spectrum_iso (prism_connected r) e,
      prism_power_spectrum r hr d hd,hell]
    rcases hr with rfl | rfl <;> simp [componentPowerSize,prismPowerSize]

/-- Complete all-positive-power classification, with no connectivity or coprimality restriction. -/
theorem all_powers_iff (n a : ℕ) (hn : 4 ≤ n) (hne : Even n)
    (ha : 1 ≤ a) (halt : a < n/2) :
    ((∀ d : ℕ, 1 ≤ d → WellCovered (graphPower (cubic n a) d)) ↔
      WellCovered (cubic n a)) ∧
      (WellCovered (cubic n a) ↔ n / Nat.gcd n a ∈ ({3,4,5,6,8} : Set ℕ)) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  refine ⟨⟨?_,?_⟩,first_wellCovered_iff n a hn hne ha halt⟩
  · intro h
    simpa only [power_one] using h 1 (by omega)
  · intro h d hd
    apply (wellCovered_power_components d).mpr
    intro C
    rw [wellCovered_iff_spectrum,component_power_spectrum n a hn hne ha halt
      ((first_wellCovered_iff n a hn hne ha halt).mp h) d hd C]
    exact Set.subsingleton_singleton

/-- The full native component multiplier, including attainability, at every positive power. -/
theorem cubic_power_spectrum (n a : ℕ) (hn : 4 ≤ n) (hne : Even n)
    (ha : 1 ≤ a) (halt : a < n/2)
    (hclass : n / Nat.gcd n a ∈ ({3,4,5,6,8} : Set ℕ)) (d : ℕ) (hd : 1 ≤ d) :
    letI : NeZero n := ⟨by omega⟩
    spectrum (graphPower (cubic n a) d) =
      {Nat.gcd a (n/2) * componentPowerSize (n / Nat.gcd n a) d} := by
  classical
  letI : NeZero n := ⟨by omega⟩
  letI : Fintype (cubic n a).ConnectedComponent := Fintype.ofFinite _
  have hc := (component_decomposition n a hn hne ha halt).1
  ext k
  rw [spectrum_power_components hd]
  constructor
  · rintro ⟨f,hf,hsum⟩
    have heq : f = fun _ => componentPowerSize (n / Nat.gcd n a) d := by
      funext C
      have hh := hf C
      rw [component_power_spectrum n a hn hne ha halt hclass d hd C] at hh
      exact hh
    rw [heq] at hsum
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,
      ← Nat.card_eq_fintype_card,hc,Set.mem_singleton_iff] using hsum.symm
  · intro hk
    have hk' : k = Nat.gcd a (n/2) * componentPowerSize (n / Nat.gcd n a) d := hk
    refine ⟨fun _ => componentPowerSize (n / Nat.gcd n a) d,?_,?_⟩
    · intro C
      rw [component_power_spectrum n a hn hne ha halt hclass d hd C]
      rfl
    · simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,
        ← Nat.card_eq_fintype_card,hc,hk']

/-- Once the exponent is at least three, every classified component is complete and
an actual maximal independent set has exactly one vertex per original component. -/
theorem eventual_spectrum (n a : ℕ) (hn : 4 ≤ n) (hne : Even n)
    (ha : 1 ≤ a) (halt : a < n/2)
    (hclass : n / Nat.gcd n a ∈ ({3,4,5,6,8} : Set ℕ)) (d : ℕ) (hd : 3 ≤ d) :
    letI : NeZero n := ⟨by omega⟩
    spectrum (graphPower (cubic n a) d) = {Nat.gcd a (n/2)} := by
  letI : NeZero n := ⟨by omega⟩
  rw [cubic_power_spectrum n a hn hne ha halt hclass d (by omega)]
  simp [componentPowerSize,show d≠1 by omega,show d≠2 by omega]

private def singleComponentIso {V : Type} {G : SimpleGraph V}
    [Subsingleton G.ConnectedComponent] (C : G.ConnectedComponent) : C.toSimpleGraph ≃g G where
  toEquiv := Equiv.ofBijective (fun v : C => v.val) ⟨Subtype.val_injective,by
    intro v
    exact ⟨⟨v,Subsingleton.elim _ _⟩,rfl⟩⟩
  map_rel_iff' := by intro u v; rfl

/-- The standard connected odd-cycle prism is the actual two-step cubic circulant. -/
private def prismCirculantIso (r : ℕ) (hr : Odd (r+3)) :
    cubic (2*(r+3)) 2 ≃g prism r := by
  let G := cubic (2*(r+3)) 2
  have hhalf : 2*(r+3)/2=r+3 := by omega
  have hcop : Nat.gcd 2 (r+3)=1 := (Nat.coprime_two_left.mpr hr).gcd_eq_one
  obtain ⟨hc,_,ho⟩ := component_decomposition (2*(r+3)) 2 (by omega)
    ⟨r+3,by omega⟩ (by omega) (by omega)
  rw [hhalf,hcop] at hc
  letI : Subsingleton G.ConnectedComponent := (Nat.card_eq_one_iff_unique.mp hc).1
  let C := G.connectedComponentMk (0 : ZMod (2*(r+3)))
  have hell : 2*(r+3) / Nat.gcd (2*(r+3)) 2 = r+3 := by
    rw [Nat.gcd_eq_right (show 2 ∣ 2*(r+3) from ⟨r+3,by omega⟩)]
    omega
  apply Classical.choice
  have hh := ho (hell.symm ▸ hr)
  obtain ⟨_,_,s,hs,he⟩ := hh
  have hsr : s=r := by omega
  subst s
  obtain ⟨e⟩ := he C
  exact ⟨(e.trans (singleComponentIso C)).symm⟩

/-- Names of the five connected cubic types in the classification. -/
inductive ConnectedType where
  | completeFour | completeBipartiteThree | triangularPrism | eightMobius | pentagonalPrism
  deriving DecidableEq

open ConnectedType

def typeOrder : ConnectedType → ℕ
  | completeFour => 4
  | completeBipartiteThree => 6
  | triangularPrism => 6
  | eightMobius => 8
  | pentagonalPrism => 10

instance typeOrderNeZero (t : ConnectedType) : NeZero (typeOrder t) := by
  cases t <;> exact ⟨by decide⟩

def typeStep : ConnectedType → ℕ
  | triangularPrism | pentagonalPrism => 2
  | _ => 1

def typeVertex : ConnectedType → Type
  | completeFour => ZMod 4
  | completeBipartiteThree => Fin 3 ⊕ Fin 3
  | triangularPrism => Fin 3 × ZMod 2
  | eightMobius => ZMod 8
  | pentagonalPrism => Fin 5 × ZMod 2

instance typeVertexFintype (t : ConnectedType) : Fintype (typeVertex t) := by cases t <;> unfold typeVertex <;> exact inferInstance
instance typeVertexDecidableEq (t : ConnectedType) : DecidableEq (typeVertex t) := by cases t <;> unfold typeVertex <;> exact inferInstance

/-- Each model is the named native graph, rather than a scalar representative. -/
def typeGraph : (t : ConnectedType) → SimpleGraph (typeVertex t)
  | completeFour => ⊤
  | completeBipartiteThree => completeBipartiteGraph (Fin 3) (Fin 3)
  | triangularPrism => prism 0
  | eightMobius => mobius 2
  | pentagonalPrism => prism 2

/-- Explicit parity coordinates for the complete bipartite six-vertex graph. -/
private def bipartiteSixIso : completeBipartiteGraph (Fin 3) (Fin 3) ≃g mobius 1 := by
  let f : Fin 3 ⊕ Fin 3 → ZMod 6 := Sum.elim
    (fun i => ((2*i.val : ℕ) : ZMod 6))
    (fun i => ((2*i.val+1 : ℕ) : ZMod 6))
  have hf : Function.Bijective f := by decide +kernel
  refine ⟨Equiv.ofBijective f hf,?_⟩
  have h : ∀ u v : Fin 3 ⊕ Fin 3,
      (mobius 1).Adj (f u) (f v) ↔ (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u v := by
    simp only [mobius,circulantGraph_adj,Set.mem_insert_iff,Set.mem_singleton_iff,
      completeBipartiteGraph_adj]
    decide +kernel
  exact h

/-- The listed cubic parameters identify the actual five native graph types. -/
def nativeTypeIso (t : ConnectedType) :
    cubic (typeOrder t) (typeStep t) ≃g typeGraph t := by
  cases t with
  | completeFour =>
    have h : mobius 0 = (⊤ : SimpleGraph (ZMod 4)) := by
      rw [← connected_power_one (mobius_connected 0)]
      exact power_eq_top_of_diam_le (mobius_connected 0) (by norm_num [mobius_diameter])
    change mobius 0 ≃g (⊤ : SimpleGraph (ZMod 4))
    simpa only [h] using (SimpleGraph.Iso.refl : mobius 0 ≃g mobius 0)
  | completeBipartiteThree => exact bipartiteSixIso.symm
  | triangularPrism => exact prismCirculantIso 0 (by decide)
  | eightMobius => exact SimpleGraph.Iso.refl
  | pentagonalPrism => exact prismCirculantIso 2 (by decide)

def typeDiameter : ConnectedType → ℕ
  | completeFour => 1
  | completeBipartiteThree | triangularPrism | eightMobius => 2
  | pentagonalPrism => 3

/-- The sequences are `(1)`, `(3,1)`, `(2,1)`, `(3,1)`, `(4,2,1)` and then one. -/
def typePowerSize (t : ConnectedType) (d : ℕ) : ℕ :=
  match t with
  | completeFour => 1
  | completeBipartiteThree | eightMobius => if d=1 then 3 else 1
  | triangularPrism => if d=1 then 2 else 1
  | pentagonalPrism => if d=1 then 4 else if d=2 then 2 else 1

/-- The full native five-type table: actual graph coordinates, exact diameters,
and attained spectra at all positive powers. -/
theorem native_type_table (t : ConnectedType) :
    Nonempty (cubic (typeOrder t) (typeStep t) ≃g typeGraph t) ∧
      (cubic (typeOrder t) (typeStep t)).Connected ∧
      (cubic (typeOrder t) (typeStep t)).diam = typeDiameter t ∧
      ∀ d : ℕ, 1 ≤ d →
        spectrum (graphPower (cubic (typeOrder t) (typeStep t)) d) = {typePowerSize t d} := by
  have hn : 4 ≤ typeOrder t := by cases t <;> decide
  letI : NeZero (typeOrder t) := ⟨by omega⟩
  have he : Even (typeOrder t) := by cases t <;> decide
  have ha : 1 ≤ typeStep t := by cases t <;> decide
  have halt : typeStep t < typeOrder t/2 := by cases t <;> decide
  have hc : typeOrder t / Nat.gcd (typeOrder t) (typeStep t) ∈ ({3,4,5,6,8} : Set ℕ) := by
    cases t <;> norm_num [typeOrder,typeStep]
  refine ⟨⟨nativeTypeIso t⟩,?_,?_,?_⟩
  · cases t with
    | completeFour => exact mobius_connected 0
    | completeBipartiteThree => exact mobius_connected 1
    | triangularPrism => exact (prismCirculantIso 0 (by decide)).connected_iff.mpr (prism_connected 0)
    | eightMobius => exact mobius_connected 2
    | pentagonalPrism => exact (prismCirculantIso 2 (by decide)).connected_iff.mpr (prism_connected 2)
  · cases t with
    | completeFour => exact mobius_diameter 0
    | completeBipartiteThree => exact mobius_diameter 1
    | triangularPrism =>
      have h := diam_iso (prismCirculantIso 0 (by decide))
      rw [prism_diameter] at h
      exact h.symm
    | eightMobius => exact mobius_diameter 2
    | pentagonalPrism =>
      have h := diam_iso (prismCirculantIso 2 (by decide))
      rw [prism_diameter] at h
      exact h.symm
  · intro d hd
    rw [cubic_power_spectrum _ _ hn he ha halt hc d hd]
    cases t <;> simp [typeOrder,typeStep,componentPowerSize,typePowerSize]

/-- Every component of every classified cubic circulant is one of the five actual native types. -/
theorem classified_component_type (n a : ℕ) (hn : 4 ≤ n) (hne : Even n)
    (ha : 1 ≤ a) (halt : a < n/2)
    (hclass : n / Nat.gcd n a ∈ ({3,4,5,6,8} : Set ℕ))
    (C : (cubic n a).ConnectedComponent) :
    ∃ t : ConnectedType,
      n / Nat.gcd n a = typeOrder t / Nat.gcd (typeOrder t) (typeStep t) ∧
      Nonempty (C.toSimpleGraph ≃g typeGraph t) := by
  obtain ⟨_,he,ho⟩ := component_decomposition n a hn hne ha halt
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hclass
  rcases Nat.even_or_odd (n / Nat.gcd n a) with hp | hp
  · obtain ⟨_,m,hell,he⟩ := he hp
    have hm : m ≤ 2 := by omega
    obtain ⟨e⟩ := he C
    interval_cases m
    · exact ⟨completeFour,by simpa [typeOrder,typeStep] using hell,
        ⟨e.symm.trans (nativeTypeIso completeFour)⟩⟩
    · exact ⟨completeBipartiteThree,by simpa [typeOrder,typeStep] using hell,
        ⟨e.symm.trans (nativeTypeIso completeBipartiteThree)⟩⟩
    · exact ⟨eightMobius,by simpa [typeOrder,typeStep] using hell,⟨e.symm⟩⟩
  · obtain ⟨_,_,r,hell,he⟩ := ho hp
    have hr : r=0 ∨ r=2 := by simp only [Nat.odd_iff] at hp; omega
    obtain ⟨e⟩ := he C
    rcases hr with rfl | rfl
    · exact ⟨triangularPrism,by simpa [typeOrder,typeStep] using hell,⟨e.symm⟩⟩
    · exact ⟨pentagonalPrism,by simpa [typeOrder,typeStep] using hell,⟨e.symm⟩⟩

end
end CubicCirculant
