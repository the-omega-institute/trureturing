/- GID: D5/S3/Combinatorics/Sequenceability/PositiveChargePorts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PositiveChargePorts
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original blue ports lift a directed spanning cycle to a literal all-coordinate word avoiding every complete Boolean row. -/

import D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
import D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton

/-! Original-coordinate port cycles and interval-avoiding words. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Sequenceability.PositiveChargePorts
open Finset
open scoped Classical
open D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
open D5.S3.Combinatorics.Graph.Walks.SemicompleteHamilton
universe u
variable {X : Type u} [DecidableEq X]

/-- EXACT integer span of the original coefficient-one H rows. No saturation,
projection, field extension or scaled relation is substituted for this lattice. -/
def originalSpan (H : Finset (Finset X)) : Submodule ℤ (X → ℤ) :=
  Submodule.span ℤ (row '' (↑H : Set (Finset X)))

/-- The actual original minimal rows in the complete integer Boolean family. -/
def minimalFamily (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) : Finset (Finset X) :=
  Ω.powerset.filter (Minimal M Ω)

/-- Literal incidence neighbourhood; no coordinate IDs are projected or merged. -/
def neighborhood (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (x : X) :
    Finset (Finset X) := (minimalFamily M Ω).filter (fun S => x ∈ S)

def terminalNeighbors (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X)
    (b : Finset X) : Finset (Finset X) :=
  (neighborhood M Ω q).filter (fun t => (b ∩ t).Nonempty)

@[simp] theorem mem_minimalFamily {M : Submodule ℤ (X → ℤ)} {Ω S : Finset X} :
    S ∈ minimalFamily M Ω ↔ S ⊆ Ω ∧ Minimal M Ω S := by
  simp [minimalFamily]

@[simp] theorem mem_neighborhood {M : Submodule ℤ (X → ℤ)}
    {Ω S : Finset X} {x : X} :
    S ∈ neighborhood M Ω x ↔ S ∈ minimalFamily M Ω ∧ x ∈ S := by
  simp [neighborhood]

@[simp] theorem mem_terminalNeighbors {M : Submodule ℤ (X → ℤ)}
    {Ω b t : Finset X} {q : X} :
    t ∈ terminalNeighbors M Ω q b ↔
      t ∈ neighborhood M Ω q ∧ (b ∩ t).Nonempty := by
  simp [terminalNeighbors]

/-- Exact local geometry already derived natively in the positive branch.
Every vertex is an ORIGINAL minimal row, and `pair` describes ALL original
minimal incidences of the shared coordinate. Outside coordinates are unrestricted.
Deriving this structure from the original charge hypotheses is a later obligation. -/
structure Geometry (M : Submodule ℤ (X → ℤ)) (Ω : Finset X) (q : X) where
  B : Finset (Finset X)
  q_mem : q ∈ Ω
  B_minimal : B ⊆ minimalFamily M Ω
  q_not_mem_B : ∀ b ∈ B, q ∉ b
  pair : ∀ b ∈ B, ∀ t ∈ neighborhood M Ω q, ∀ x ∈ b, x ∈ t →
    neighborhood M Ω x = {t, b}
  degree : ∀ b ∈ B, 2 ≤ (terminalNeighbors M Ω q b).card
  coverage : ∀ s ∈ neighborhood M Ω q, ∀ t ∈ neighborhood M Ω q, s ≠ t →
    ∃ b ∈ B, s ∈ terminalNeighbors M Ω q b ∧ t ∈ terminalNeighbors M Ω q b
  no_universal : ∀ b ∈ B, ∃ t ∈ neighborhood M Ω q,
    t ∉ terminalNeighbors M Ω q b

variable {M : Submodule ℤ (X → ℤ)} {Ω : Finset X} {q : X}

theorem Geometry.B_ne_terminal (G : Geometry M Ω q) {b t : Finset X}
    (hb : b ∈ G.B) (ht : t ∈ neighborhood M Ω q) : b ≠ t := by
  intro he
  exact G.q_not_mem_B b hb (he.symm ▸ (mem_neighborhood.mp ht).2)

theorem Geometry.pair_unique (G : Geometry M Ω q) {x : X} {b d s t : Finset X}
    (hb : b ∈ G.B) (hd : d ∈ G.B)
    (hs : s ∈ neighborhood M Ω q) (ht : t ∈ neighborhood M Ω q)
    (hx : neighborhood M Ω x = {s,b})
    (hy : neighborhood M Ω x = {t,d}) : s = t ∧ b = d := by
  have hs' : s ∈ ({t,d} : Finset (Finset X)) := by rw [← hy, hx]; simp
  have hb' : b ∈ ({t,d} : Finset (Finset X)) := by rw [← hy, hx]; simp
  have hst : s = t := by
    rcases Finset.mem_insert.mp hs' with he | he
    · exact he
    · have hsd : s = d := by simpa using he
      exact ((G.B_ne_terminal hd hs) hsd.symm).elim
  have hbd : b = d := by
    rcases Finset.mem_insert.mp hb' with he | he
    · exact ((G.B_ne_terminal hb ht) he).elim
    · simpa using he
  exact ⟨hst,hbd⟩

/-- `true` means blue at this terminal. At b0 precisely z is red; at every
other B row precisely its least terminal neighbour is red. -/
def blueAt (G : Geometry M Ω q) (b0 z : Finset X)
    (rank : Finset X → ℕ) (b t : Finset X) : Prop :=
  if b = b0 then t ≠ z else
    ∃ s ∈ terminalNeighbors M Ω q b, rank s < rank t

def localBlue (G : Geometry M Ω q) (b0 z : Finset X)
    (rank : Finset X → ℕ) : Finset X :=
  (Ω.erase q).filter (fun x => ∃ b ∈ G.B, ∃ t ∈ neighborhood M Ω q,
    x ∈ b ∧ x ∈ t ∧ blueAt G b0 z rank b t)

/-- K contains the chosen exterior blue ORIGINAL coordinates. -/
def blue (G : Geometry M Ω q) (b0 z : Finset X)
    (rank : Finset X → ℕ) (K : Finset X) : Finset X :=
  localBlue G b0 z rank ∪ K

def red (G : Geometry M Ω q) (b0 z : Finset X)
    (rank : Finset X → ℕ) (K : Finset X) : Finset X :=
  Ω \ insert q (blue G b0 z rank K)

theorem blue_subset (G : Geometry M Ω q) (b0 z : Finset X)
    (rank : Finset X → ℕ) {K : Finset X} (hK : K ⊆ Ω.erase q) :
    blue G b0 z rank K ⊆ Ω.erase q := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (Finset.mem_filter.mp hx).1
  · exact hK hx

/-- The explicit colouring really restricts to the specified colour on every
original parallel port. Canonical two-endpoint incidence supplies uniqueness. -/
theorem port_colour (G : Geometry M Ω q) (b0 z : Finset X)
    (rank : Finset X → ℕ) {K : Finset X}
    (hKB : ∀ b ∈ G.B, Disjoint K b)
    {b t : Finset X} (hb : b ∈ G.B) (ht : t ∈ neighborhood M Ω q)
    {x : X} (hxb : x ∈ b) (hxt : x ∈ t) :
    x ∈ blue G b0 z rank K ↔ blueAt G b0 z rank b t := by
  have hxΩ : x ∈ Ω := (mem_minimalFamily.mp (G.B_minimal hb)).1 hxb
  have hxq : x ≠ q := by rintro rfl; exact G.q_not_mem_B b hb hxb
  have hxK : x ∉ K := fun h => Finset.disjoint_left.mp (hKB b hb) h hxb
  constructor
  · intro hx
    have hxL : x ∈ localBlue G b0 z rank :=
      (Finset.mem_union.mp hx).resolve_right hxK
    obtain ⟨d,hd,s,hs,hxd,hxs,hc⟩ := (Finset.mem_filter.mp hxL).2
    obtain ⟨hst,hdb⟩ := G.pair_unique hd hb hs ht
      (G.pair d hd s hs x hxd hxs) (G.pair b hb t ht x hxb hxt)
    simpa [hst,hdb] using hc
  · intro hc
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    exact ⟨by simp [hxΩ,hxq], b,hb,t,ht,hxb,hxt,hc⟩

theorem red_port (G : Geometry M Ω q) (b0 z : Finset X)
    (rank : Finset X → ℕ) {K : Finset X}
    (hKB : ∀ b ∈ G.B, Disjoint K b)
    {b t : Finset X} (hb : b ∈ G.B) (ht : t ∈ neighborhood M Ω q)
    {x : X} (hxb : x ∈ b) (hxt : x ∈ t)
    (hc : ¬blueAt G b0 z rank b t) : x ∈ red G b0 z rank K := by
  have hxΩ := (mem_minimalFamily.mp (G.B_minimal hb)).1 hxb
  have hxq : x ≠ q := by rintro rfl; exact G.q_not_mem_B b hb hxb
  have hxb' : x ∉ blue G b0 z rank K :=
    fun h => hc ((port_colour G b0 z rank hKB hb ht hxb hxt).mp h)
  simp [red,hxΩ,hxq,hxb']

/-- The actual relation asks for a BLUE ORIGINAL coordinate at the target;
the same B witness is allowed on arbitrarily many arcs. -/
def arc (G : Geometry M Ω q) (Blue : Finset X) (s t : Finset X) : Prop :=
  s ∈ neighborhood M Ω q ∧ t ∈ neighborhood M Ω q ∧ s ≠ t ∧
    ∃ b ∈ G.B, s ∈ terminalNeighbors M Ω q b ∧
      ∃ x ∈ b ∩ t, x ∈ Blue

theorem arc_of_colour (G : Geometry M Ω q) (b0 z : Finset X)
    (rank : Finset X → ℕ) {K : Finset X}
    (hKB : ∀ b ∈ G.B, Disjoint K b)
    {b s t : Finset X} (hb : b ∈ G.B)
    (hs : s ∈ terminalNeighbors M Ω q b) (ht : t ∈ terminalNeighbors M Ω q b)
    (hst : s ≠ t) (hc : blueAt G b0 z rank b t) :
    arc G (blue G b0 z rank K) s t := by
  obtain ⟨x,hx⟩ := (mem_terminalNeighbors.mp ht).2
  have hxt := Finset.mem_inter.mp hx
  exact ⟨(mem_terminalNeighbors.mp hs).1,(mem_terminalNeighbors.mp ht).1,hst,
    b,hb,hs,x,hx,(port_colour G b0 z rank hKB hb
      (mem_terminalNeighbors.mp ht).1 hxt.1 hxt.2).mpr hc⟩

theorem semicomplete (G : Geometry M Ω q) (b0 z : Finset X)
    (rank : Finset X → ℕ)
    (hrank : ∀ s ∈ neighborhood M Ω q, ∀ t ∈ neighborhood M Ω q,
      rank s = rank t → s = t)
    {K : Finset X} (hKB : ∀ b ∈ G.B, Disjoint K b)
    {s t : Finset X} (hs : s ∈ neighborhood M Ω q)
    (ht : t ∈ neighborhood M Ω q) (hst : s ≠ t) :
    arc G (blue G b0 z rank K) s t ∨ arc G (blue G b0 z rank K) t s := by
  obtain ⟨b,hb,hsb,htb⟩ := G.coverage s hs t ht hst
  by_cases hb0 : b = b0
  · by_cases htz : t = z
    · right
      have hsz : s ≠ z := fun he => hst (he.trans htz.symm)
      apply arc_of_colour G b0 z rank hKB hb htb hsb hst.symm
      simp [blueAt,hb0,hsz]
    · left
      exact arc_of_colour G b0 z rank hKB hb hsb htb hst (by simp [blueAt,hb0,htz])
  · by_cases hlt : rank s < rank t
    · left
      exact arc_of_colour G b0 z rank hKB hb hsb htb hst
        (by simp only [blueAt,ite_eq_right hb0]; exact ⟨s,hsb,hlt⟩)
    · right
      have hne : rank s ≠ rank t := fun he => hst (hrank s hs t ht he)
      have hts : rank t < rank s := by omega
      exact arc_of_colour G b0 z rank hKB hb htb hsb hst.symm
        (by simp only [blueAt,ite_eq_right hb0]; exact ⟨t,htb,hts⟩)

/-- Explicit b0,a,z,u paths establish strong connectivity. Pair coverage alone
is NOT a strong-connectivity hypothesis. -/
theorem stronglyConnected (G : Geometry M Ω q) (b0 a z u : Finset X)
    (rank : Finset X → ℕ) (hb0 : b0 ∈ G.B)
    (ha : a ∈ terminalNeighbors M Ω q b0)
    (hz : z ∈ terminalNeighbors M Ω q b0) (haz : a ≠ z)
    (hu : u ∈ neighborhood M Ω q) (hu0 : u ∉ terminalNeighbors M Ω q b0)
    (hrank : ∀ s ∈ neighborhood M Ω q, ∀ t ∈ neighborhood M Ω q,
      rank s = rank t → s = t)
    (hmin : ∀ t ∈ neighborhood M Ω q, rank a ≤ rank t)
    (hmax : ∀ t ∈ neighborhood M Ω q, rank t ≤ rank z)
    {K : Finset X} (hKB : ∀ b ∈ G.B, Disjoint K b) :
    ∀ s ∈ neighborhood M Ω q, ∀ t ∈ neighborhood M Ω q,
      Relation.ReflTransGen (arc G (blue G b0 z rank K)) s t := by
  let D := arc G (blue G b0 z rank K)
  have haT := (mem_terminalNeighbors.mp ha).1
  have hzT := (mem_terminalNeighbors.mp hz).1
  have outside (x : Finset X) (hx : x ∈ neighborhood M Ω q)
      (hx0 : x ∉ terminalNeighbors M Ω q b0) : D a x ∧ D x z := by
    have hax : a ≠ x := by rintro rfl; exact hx0 ha
    have hxz : x ≠ z := by rintro rfl; exact hx0 hz
    obtain ⟨b,hb,hab,hxb⟩ := G.coverage a haT x hx hax
    have hb' : b ≠ b0 := by rintro rfl; exact hx0 hxb
    have hlt : rank a < rank x := by
      have hle := hmin x hx
      have hne : rank a ≠ rank x := fun he => hax (hrank a haT x hx he)
      omega
    have hax' : D a x := arc_of_colour G b0 z rank hKB hb hab hxb hax
      (by simp only [blueAt,ite_eq_right hb']; exact ⟨a,hab,hlt⟩)
    obtain ⟨c,hc,hxc,hzc⟩ := G.coverage x hx z hzT hxz
    have hc' : c ≠ b0 := by rintro rfl; exact hx0 hxc
    have hlt' : rank x < rank z := by
      have hle := hmax x hx
      have hne : rank x ≠ rank z := fun he => hxz (hrank x hx z hzT he)
      omega
    exact ⟨hax',arc_of_colour G b0 z rank hKB hc hxc hzc hxz
      (by simp only [blueAt,ite_eq_right hc']; exact ⟨x,hxc,hlt'⟩)⟩
  have hza : D z a := arc_of_colour G b0 z rank hKB hb0 hz ha haz.symm
    (by simp [blueAt,haz])
  have hauz := outside u hu hu0
  have routes (x : Finset X) (hx : x ∈ neighborhood M Ω q) :
      Relation.ReflTransGen D a x ∧ Relation.ReflTransGen D x a := by
    by_cases hxa : x = a
    · subst x
      exact ⟨.refl,.refl⟩
    by_cases hx0 : x ∈ terminalNeighbors M Ω q b0
    · by_cases hxz : x = z
      · subst x
        exact ⟨(Relation.ReflTransGen.single hauz.1).tail hauz.2,
          Relation.ReflTransGen.single hza⟩
      · have hax : D a x := arc_of_colour G b0 z rank hKB hb0 ha hx0 (Ne.symm hxa)
          (by simp [blueAt,hxz])
        have hxa' : D x a := arc_of_colour G b0 z rank hKB hb0 hx0 ha hxa
          (by simp [blueAt,haz])
        exact ⟨.single hax,.single hxa'⟩
    · have h := outside x hx hx0
      exact ⟨.single h.1,(Relation.ReflTransGen.single h.2).tail hza⟩
  intro s hs t ht
  exact ((routes s hs).2).trans (routes t ht).1

/-- Every B star is mixed for the actual native colouring, including all its
parallel ports. The exterior mixed-star input is separate. -/
theorem mixed_B (G : Geometry M Ω q) (b0 z : Finset X)
    (rank : Finset X → ℕ) (hz : z ∈ terminalNeighbors M Ω q b0)
    (hrank : ∀ s ∈ neighborhood M Ω q, ∀ t ∈ neighborhood M Ω q,
      rank s = rank t → s = t)
    {K : Finset X} (hKB : ∀ b ∈ G.B, Disjoint K b)
    {b : Finset X} (hb : b ∈ G.B) :
    (∃ x ∈ b, x ∈ red G b0 z rank K) ∧
      (∃ y ∈ b, y ∈ blue G b0 z rank K) := by
  have hdeg := G.degree b hb
  have another {t : Finset X} (ht : t ∈ terminalNeighbors M Ω q b) :
      ∃ s ∈ terminalNeighbors M Ω q b, s ≠ t := by
    by_contra hn
    have hall : ∀ s ∈ terminalNeighbors M Ω q b, s = t := by
      intro s hs
      by_contra hst
      exact hn ⟨s,hs,hst⟩
    have hsub : terminalNeighbors M Ω q b ⊆ {t} := by
      intro s hs
      simpa using hall s hs
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  by_cases hb0 : b = b0
  · subst b
    obtain ⟨s,hs,hsz⟩ := another hz
    obtain ⟨x,hx⟩ := (mem_terminalNeighbors.mp hz).2
    obtain ⟨y,hy⟩ := (mem_terminalNeighbors.mp hs).2
    have hx' := Finset.mem_inter.mp hx
    have hy' := Finset.mem_inter.mp hy
    refine ⟨⟨x,hx'.1,red_port G b0 z rank hKB hb
      (mem_terminalNeighbors.mp hz).1 hx'.1 hx'.2 (by simp [blueAt])⟩,
      y,hy'.1,?_⟩
    exact (port_colour G b0 z rank hKB hb (mem_terminalNeighbors.mp hs).1
      hy'.1 hy'.2).mpr (by simp [blueAt,hsz])
  · have hne : (terminalNeighbors M Ω q b).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨t,ht,hmin⟩ := Finset.exists_min_image (terminalNeighbors M Ω q b) rank hne
    obtain ⟨s,hs,hst⟩ := another ht
    have hlt : rank t < rank s := by
      have hle := hmin s hs
      have hneq : rank t ≠ rank s := fun he => hst
        (hrank t (mem_terminalNeighbors.mp ht).1 s
          (mem_terminalNeighbors.mp hs).1 he).symm
      omega
    obtain ⟨x,hx⟩ := (mem_terminalNeighbors.mp ht).2
    obtain ⟨y,hy⟩ := (mem_terminalNeighbors.mp hs).2
    have hx' := Finset.mem_inter.mp hx
    have hy' := Finset.mem_inter.mp hy
    have hred : ¬blueAt G b0 z rank b t := by
      simp only [blueAt,ite_eq_right hb0]
      rintro ⟨v,hv,hvlt⟩
      have := hmin v hv
      omega
    refine ⟨⟨x,hx'.1,red_port G b0 z rank hKB hb
      (mem_terminalNeighbors.mp ht).1 hx'.1 hx'.2 hred⟩,y,hy'.1,?_⟩
    exact (port_colour G b0 z rank hKB hb (mem_terminalNeighbors.mp hs).1
      hy'.1 hy'.2).mpr (by
        simp only [blueAt,ite_eq_right hb0]
        exact ⟨t,ht,hlt⟩)

/-- alpha is selected on the ACTUAL a--u common neighbour, beta on z--b0. -/
theorem red_frame (G : Geometry M Ω q) (b0 a z u : Finset X)
    (rank : Finset X → ℕ) (hb0 : b0 ∈ G.B)
    (ha : a ∈ terminalNeighbors M Ω q b0)
    (hz : z ∈ terminalNeighbors M Ω q b0) (haz : a ≠ z)
    (hu : u ∈ neighborhood M Ω q) (hu0 : u ∉ terminalNeighbors M Ω q b0)
    (hmin : ∀ t ∈ neighborhood M Ω q, rank a ≤ rank t)
    {K : Finset X} (hKB : ∀ b ∈ G.B, Disjoint K b) :
    ∃ alpha beta : X,
      alpha ∈ a ∧ alpha ∈ red G b0 z rank K ∧ beta ∈ red G b0 z rank K ∧
      alpha ≠ beta ∧ neighborhood M Ω beta = {z,b0} := by
  have haT := (mem_terminalNeighbors.mp ha).1
  have hzT := (mem_terminalNeighbors.mp hz).1
  have hau : a ≠ u := by rintro rfl; exact hu0 ha
  obtain ⟨b,hb,hab,hub⟩ := G.coverage a haT u hu hau
  have hb' : b ≠ b0 := by rintro rfl; exact hu0 hub
  obtain ⟨alpha,halpha⟩ := (mem_terminalNeighbors.mp hab).2
  obtain ⟨beta,hbeta⟩ := (mem_terminalNeighbors.mp hz).2
  have hα := Finset.mem_inter.mp halpha
  have hβ := Finset.mem_inter.mp hbeta
  have hαc : ¬blueAt G b0 z rank b a := by
    simp only [blueAt,ite_eq_right hb']
    rintro ⟨s,hs,hlt⟩
    have := hmin s (mem_terminalNeighbors.mp hs).1
    omega
  have hβN := G.pair b0 hb0 z hzT beta hβ.1 hβ.2
  have hαβ : alpha ≠ beta := by
    intro he
    have hn := G.pair b hb a haT alpha hα.1 hα.2
    have hβN' : neighborhood M Ω alpha = {z,b0} := he.symm ▸ hβN
    exact haz (G.pair_unique hb hb0 haT hzT hn hβN').1
  exact ⟨alpha,beta,hα.2,
    red_port G b0 z rank hKB hb haT hα.1 hα.2 hαc,
    red_port G b0 z rank hKB hb0 hzT hβ.1 hβ.2 (by simp [blueAt]),hαβ,hβN⟩

/-- Genuine independent-star geometry on the live word-construction path.
No individual forbidden-coordinate conclusions are assumed. -/
def Independent (Q : Finset (Finset X)) : Prop :=
  ∀ S ∈ Q, ∀ D ∈ Q, S ≠ D → Disjoint S D

theorem selected_unique {Q : Finset (Finset X)} (hQ : Independent Q)
    {S D : Finset X} (hS : S ∈ Q) (hD : D ∈ Q)
    {x : X} (hxS : x ∈ S) (hxD : x ∈ D) : S = D := by
  by_contra hne
  exact Finset.disjoint_left.mp (hQ S hS D hD hne) hxS hxD

theorem selected_terminal_unique {Q : Finset (Finset X)} (hQ : Independent Q)
    {s t : Finset X} (hs : s ∈ Q) (ht : t ∈ Q)
    (hsT : s ∈ neighborhood M Ω q) (htT : t ∈ neighborhood M Ω q) : s = t := by
  exact selected_unique hQ hs ht (mem_neighborhood.mp hsT).2 (mem_neighborhood.mp htT).2

/-- If t is selected, an original port at a different terminal s and at a
B-neighbour of t is absent from the ENTIRE selected union. Extra exterior
stars cannot supply it because its canonical neighbourhood is exactly {s,b}. -/
theorem forbidden_port (G : Geometry M Ω q)
    {Q : Finset (Finset X)} (hQP : Q ⊆ minimalFamily M Ω) (hQ : Independent Q)
    {t s b : Finset X} (htQ : t ∈ Q) (htT : t ∈ neighborhood M Ω q)
    (hsT : s ∈ neighborhood M Ω q) (hst : s ≠ t) (hb : b ∈ G.B)
    (htb : t ∈ terminalNeighbors M Ω q b)
    {x : X} (hxN : neighborhood M Ω x = {s,b}) : x ∉ Q.biUnion id := by
  intro hx
  obtain ⟨D,hDQ,hxD⟩ := Finset.mem_biUnion.mp hx
  have hDN : D ∈ neighborhood M Ω x := mem_neighborhood.mpr ⟨hQP hDQ,hxD⟩
  rw [hxN] at hDN
  rcases Finset.mem_insert.mp hDN with hDs | hDb
  · subst D
    exact hst (selected_terminal_unique hQ hDQ htQ hsT htT)
  · have hDb' : D = b := by simpa using hDb
    subst D
    obtain ⟨y,hy⟩ := (mem_terminalNeighbors.mp htb).2
    have hy' := Finset.mem_inter.mp hy
    exact G.B_ne_terminal hb htT (selected_unique hQ hDQ htQ hy'.1 hy'.2)

/-- The cycle data is literal and finite. Entries are in REVERSE cyclic order,
starting at a: (a,xi_r),(t_r,xi_(r-1)),...,(t_2,xi_1).
Step e f records f.terminal -> e.terminal using e.port itself. Closing the
chain records the remaining arc from a. B witnesses are NOT required distinct.
exists_portCycle below supplies this structure from the actual strongly
connected semicomplete relation; it is not a hidden typeclass or premise. -/
def PortStep (G : Geometry M Ω q) (e f : Finset X × X) : Prop :=
  ∃ b ∈ G.B, neighborhood M Ω e.2 = {e.1,b} ∧
    f.1 ∈ terminalNeighbors M Ω q b

structure PortCycle (G : Geometry M Ω q) (Blue : Finset X) (a : Finset X) where
  first : Finset X × X
  tail : List (Finset X × X)
  first_terminal : first.1 = a
  terminals_nodup : ((first :: tail).map Prod.fst).Nodup
  terminals_cover : ((first :: tail).map Prod.fst).toFinset = neighborhood M Ω q
  port_blue : ∀ e ∈ first :: tail, e.2 ∈ Blue
  port_incidence : ∀ e ∈ first :: tail, ∃ b ∈ G.B,
    neighborhood M Ω e.2 = {e.1,b}
  steps : List.IsChain (PortStep G) ((first :: tail) ++ [first])


/-- Lift an actual reverse directed path to original blue ports, choosing the
port at each terminal from its outgoing edge in reverse order. The last step
works for every pair whose terminal is c, so the same construction closes at
its first pair. No distinctness of B witnesses is assumed or needed. -/
private theorem lift_port_path (G : Geometry M Ω q) {Blue : Finset X}
    {t c : Finset X} {l : List (Finset X)}
    (hc : List.IsChain (fun s t => arc G Blue t s) (t :: (l ++ [c]))) :
    ∃ (e : Finset X × X) (es : List (Finset X × X)),
      e.1 = t ∧ es.map Prod.fst = l ∧
      (∀ f ∈ e :: es, f.2 ∈ Blue) ∧
      (∀ f ∈ e :: es, ∃ b ∈ G.B, neighborhood M Ω f.2 = {f.1,b}) ∧
      ∀ f : Finset X × X, f.1 = c →
        List.IsChain (PortStep G) ((e :: es) ++ [f]) := by
  induction l generalizing t with
  | nil =>
    obtain ⟨hcT,htT,hct,b,hb,hcb,x,hxt,hxB⟩ := hc.rel
    have hx := Finset.mem_inter.mp hxt
    have hxN := G.pair b hb t htT x hx.1 hx.2
    refine ⟨(t,x),[],rfl,rfl,?_,?_,?_⟩
    · intro f hf
      have hf' : f = (t,x) := by simpa using hf
      simpa [hf'] using hxB
    · intro f hf
      have hf' : f = (t,x) := by simpa using hf
      exact ⟨b,hb,by simpa [hf'] using hxN⟩
    · intro f hf
      apply List.isChain_pair.mpr
      exact ⟨b,hb,hxN,by simpa [hf] using hcb⟩
  | cons s l ih =>
    obtain ⟨hsT,htT,hst,b,hb,hsb,x,hxt,hxB⟩ := hc.rel
    have hx := Finset.mem_inter.mp hxt
    have hxN := G.pair b hb t htT x hx.1 hx.2
    obtain ⟨e,es,he,hes,hblue,hinc,hsteps⟩ := ih hc.tail
    refine ⟨(t,x),e :: es,rfl,?_,?_,?_,?_⟩
    · simpa only [List.map_cons,he,hes]
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hxB
      · exact hblue f hf
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨b,hb,hxN⟩
      · exact hinc f hf
    · intro f hf
      apply List.IsChain.cons_cons
      · exact ⟨b,hb,hxN,by simpa [he] using hsb⟩
      · exact hsteps f hf

/-- Construct the actual original-port Hamilton cycle from the proved native
semicompleteness and strong connectivity. Applying the generic theorem to the
reverse relation gives exactly the orientation required by PortStep. Blue IDs
are chosen from ORIGINAL arc witnesses. Their distinctness is subsequently
proved by the existing PortCycle.ports_nodup from distinct terminal endpoints.
-/
theorem exists_portCycle (G : Geometry M Ω q) (b0 a z u : Finset X)
    (rank : Finset X → ℕ) (hb0 : b0 ∈ G.B)
    (ha : a ∈ terminalNeighbors M Ω q b0)
    (hz : z ∈ terminalNeighbors M Ω q b0) (haz : a ≠ z)
    (hu : u ∈ neighborhood M Ω q) (hu0 : u ∉ terminalNeighbors M Ω q b0)
    (hrank : ∀ s ∈ neighborhood M Ω q, ∀ t ∈ neighborhood M Ω q,
      rank s = rank t → s = t)
    (hmin : ∀ t ∈ neighborhood M Ω q, rank a ≤ rank t)
    (hmax : ∀ t ∈ neighborhood M Ω q, rank t ≤ rank z)
    {K : Finset X} (hKB : ∀ b ∈ G.B, Disjoint K b) :
    Nonempty (PortCycle G (blue G b0 z rank K) a) := by
  let T := neighborhood M Ω q
  let D := fun s t : Finset X => arc G (blue G b0 z rank K) t s
  have haT : a ∈ T := (mem_terminalNeighbors.mp ha).1
  have hzT : z ∈ T := (mem_terminalNeighbors.mp hz).1
  have hsize : 2 ≤ T.card := by
    have h := Finset.one_lt_card.mpr ⟨a,haT,z,hzT,haz⟩
    omega
  have hD : ∀ {s t}, D s t → s ∈ T ∧ t ∈ T := by
    intro s t h
    exact ⟨h.2.1,h.1⟩
  have hsemi : ∀ s ∈ T, ∀ t ∈ T, s ≠ t → D s t ∨ D t s := by
    intro s hs t ht hst
    rcases semicomplete G b0 z rank hrank hKB hs ht hst with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hstrong : ∀ s ∈ T, ∀ t ∈ T, Relation.ReflTransGen D s t := by
    intro s hs t ht
    exact (Relation.reflTransGen_swap
      (r := arc G (blue G b0 z rank K)) (a := s) (b := t)).mpr
      (stronglyConnected G b0 a z u rank hb0 ha hz haz hu hu0
        hrank hmin hmax hKB t ht s hs)
  obtain ⟨l,hn,hcover,_hlen,hchain⟩ :=
    finite_semicomplete_hamilton T D hD hsize hsemi hstrong a haT
  obtain ⟨e,es,he,hes,hblue,hinc,hsteps⟩ := lift_port_path G hchain
  have hmap : (e :: es).map Prod.fst = a :: l := by
    simp only [List.map_cons,he,hes]
  exact ⟨{
    first := e
    tail := es
    first_terminal := he
    terminals_nodup := by rw [hmap]; exact hn
    terminals_cover := by rw [hmap]; exact hcover
    port_blue := hblue
    port_incidence := hinc
    steps := hsteps e he
  }⟩

theorem PortCycle.terminal_mem (G : Geometry M Ω q)
    {Blue : Finset X} {a : Finset X} (C : PortCycle G Blue a)
    {e : Finset X × X} (he : e ∈ C.first :: C.tail) :
    e.1 ∈ neighborhood M Ω q := by
  rw [← C.terminals_cover]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)

/-- Distinct ORIGINAL blue IDs follow from distinct terminal endpoints alone. -/
theorem PortCycle.ports_nodup (G : Geometry M Ω q)
    {Blue : Finset X} {a : Finset X} (C : PortCycle G Blue a) :
    ((C.first :: C.tail).map Prod.snd).Nodup := by
  have hn : (C.first :: C.tail).Nodup := C.terminals_nodup.of_map Prod.fst
  apply hn.map_on
  intro e he f hf hef
  obtain ⟨b,hb,heN⟩ := C.port_incidence e he
  obtain ⟨d,hd,hfN⟩ := C.port_incidence f hf
  have hfN' : neighborhood M Ω e.2 = {f.1,d} := hef.symm ▸ hfN
  have hfst := (G.pair_unique hb hd (C.terminal_mem G he)
    (C.terminal_mem G hf) heN hfN').1
  exact Prod.ext hfst hef

/-- An interval joining both sides of a separator contains the separator. -/
private theorem infix_crosses {w t L R : List X} {c x y : X}
    (hn : w.Nodup) (ht : t <:+: w) (he : w = L ++ c :: R)
    (hxL : x ∈ L) (hyR : y ∈ R) (hxt : x ∈ t) (hyt : y ∈ t) : c ∈ t := by
  rw [he] at hn ht
  by_contra hct
  have hd := (List.nodup_append.mp hn).2.2
  rcases infix_avoid_separator ht hct with hL | hR
  · exact hd y (hL.subset hyt) y (by simp [hyR]) rfl
  · exact hd x hxL x (by simp [hR.subset hxt]) rfl

private theorem predecessor {Y : Type*} {a f : Y} {l : List Y} (hf : f ∈ l) :
    ∃ p e s, a :: l = p ++ e :: f :: s := by
  induction l generalizing a with
  | nil => simp at hf
  | cons b l ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨[],a,l,rfl⟩
    · obtain ⟨p,e,s,he⟩ := ih (a := b) hf
      exact ⟨a :: p,e,s,by simpa only [List.cons_append] using congrArg (List.cons a) he⟩

/-- Literally (R\\{alpha,beta}),alpha,beta,q,xi_r,...,xi_1,
(Blue\\{xi_1,...,xi_r}). Residual coordinates are enumerated, not discarded. -/
def cycleWord (Ω Blue : Finset X) (q alpha beta : X) (P : List X) : List X :=
  ((Ω \ insert q Blue) \ {alpha,beta}).toList ++
    alpha :: beta :: q :: (P ++ (Blue \ P.toFinset).toList)

theorem cycleWord_perm {Ω Blue : Finset X} {q alpha beta : X} {P : List X}
    (hq : q ∈ Ω) (hBlue : Blue ⊆ Ω.erase q)
    (hα : alpha ∈ Ω \ insert q Blue) (hβ : beta ∈ Ω \ insert q Blue)
    (hαβ : alpha ≠ beta) (hP : P.Nodup) (hPB : ∀ x ∈ P, x ∈ Blue) :
    (cycleWord Ω Blue q alpha beta P).Nodup ∧
      (cycleWord Ω Blue q alpha beta P).Perm Ω.toList := by
  let U := ((Ω \ insert q Blue) \ {alpha,beta}).toList
  let V := (Blue \ P.toFinset).toList
  let w := cycleWord Ω Blue q alpha beta P
  have hαΩ := (Finset.mem_sdiff.mp hα).1
  have hβΩ := (Finset.mem_sdiff.mp hβ).1
  have hαq : alpha ≠ q := by
    intro he
    exact (Finset.mem_sdiff.mp hα).2 (by simp [he])
  have hβq : beta ≠ q := by
    intro he
    exact (Finset.mem_sdiff.mp hβ).2 (by simp [he])
  have hαB : alpha ∉ Blue := fun hx =>
    (Finset.mem_sdiff.mp hα).2 (Finset.mem_insert_of_mem hx)
  have hβB : beta ∉ Blue := fun hx =>
    (Finset.mem_sdiff.mp hβ).2 (Finset.mem_insert_of_mem hx)
  have hqB : q ∉ Blue := by
    intro hx
    exact (Finset.mem_erase.mp (hBlue hx)).1 rfl
  have hPV (x : X) (hx : x ∈ P ++ V) : x ∈ Blue := by
    rcases List.mem_append.mp hx with hx | hx
    · exact hPB x hx
    · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1
  have hPVnd : (P ++ V).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hP,Finset.nodup_toList _,?_⟩
    intro x hx y hy he
    subst y
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hy)).2
      (List.mem_toFinset.mpr hx)
  have hαPV : alpha ∉ P ++ V := fun hx => hαB (hPV alpha hx)
  have hβPV : beta ∉ P ++ V := fun hx => hβB (hPV beta hx)
  have hqPV : q ∉ P ++ V := fun hx => hqB (hPV q hx)
  have htail : (alpha :: beta :: q :: (P ++ V)).Nodup := by
    simp [List.nodup_cons,hαβ,hαq,hβq,hαPV,hβPV,hqPV,hPVnd]
  have hn : w.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨Finset.nodup_toList _,htail,?_⟩
    intro x hx y hy he
    subst y
    have hx' := Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)
    rcases List.mem_cons.mp hy with he | hy
    · exact hx'.2 (by simp [he])
    rcases List.mem_cons.mp hy with he | hy
    · exact hx'.2 (by simp [he])
    rcases List.mem_cons.mp hy with he | hy
    · exact (Finset.mem_sdiff.mp hx'.1).2 (by simp [he])
    · exact (Finset.mem_sdiff.mp hx'.1).2 (Finset.mem_insert_of_mem (hPV x hy))
  have hm (x : X) : x ∈ w ↔ x ∈ Ω := by
    change x ∈ U ++ alpha :: beta :: q :: (P ++ V) ↔ x ∈ Ω
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp
          (Finset.mem_toList.mp hx)).1).1
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hαΩ
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hβΩ
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hq
      · exact (Finset.mem_erase.mp (hBlue (hPV x hx))).2
    · intro hxΩ
      by_cases hxα : x = alpha
      · simp [hxα]
      by_cases hxβ : x = beta
      · simp [hxβ]
      by_cases hxq : x = q
      · simp [hxq]
      by_cases hxB : x ∈ Blue
      · by_cases hxP : x ∈ P
        · simp [hxP]
        · have hxV : x ∈ V := by simp [V,hxB,hxP]
          simp [hxV]
      · have hxU : x ∈ U := by simp [U,hxΩ,hxα,hxβ,hxq,hxB]
        simp [hxU]
  exact ⟨hn,(List.perm_ext_iff_of_nodup hn Ω.nodup_toList).mpr
    (fun x => by simpa only [Finset.mem_toList] using hm x)⟩

/-- A conditional ORIGINAL all-C endpoint. Its inputs are geometric cycle data
and an explicit disjoint Boolean decomposition, not atomic interval contradictions.
All q-free unions, larger rows, exterior stars, unused IDs and parallel ports
are handled in this proof. It makes no primitive or fullGood assertion. -/
theorem avoiding_word_of_portCycle (G : Geometry M Ω q)
    {Blue : Finset X} (hBlue : Blue ⊆ Ω.erase q)
    {b0 a z : Finset X} (hb0 : b0 ∈ G.B)
    (ha : a ∈ terminalNeighbors M Ω q b0)
    (hz : z ∈ neighborhood M Ω q) (haz : a ≠ z)
    (C : PortCycle G Blue a)
    {alpha beta : X} (hαa : alpha ∈ a)
    (hαR : alpha ∈ Ω \ insert q Blue) (hβR : beta ∈ Ω \ insert q Blue)
    (hαβ : alpha ≠ beta) (hβN : neighborhood M Ω beta = {z,b0})
    (hmixed : ∀ S ∈ minimalFamily M Ω, q ∉ S →
      (∃ x ∈ S, x ∈ Ω \ insert q Blue) ∧ (∃ y ∈ S, y ∈ Blue))
    (hdecomp : ∀ A, Complete M Ω A →
      ∃ Q : Finset (Finset X), Q ⊆ minimalFamily M Ω ∧ Independent Q ∧
        A = Q.biUnion id) :
    let P := (C.first :: C.tail).map Prod.snd
    let w := cycleWord Ω Blue q alpha beta P
    w.Perm Ω.toList ∧ ∀ t : List X, t <:+: w → ¬Complete M Ω t.toFinset := by
  let P := (C.first :: C.tail).map Prod.snd
  let U := ((Ω \ insert q Blue) \ {alpha,beta}).toList
  let V := (Blue \ P.toFinset).toList
  let w := cycleWord Ω Blue q alpha beta P
  have hPB (x : X) (hx : x ∈ P) : x ∈ Blue := by
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact C.port_blue e he
  obtain ⟨hn,hperm⟩ := cycleWord_perm G.q_mem hBlue hαR hβR hαβ
    (C.ports_nodup G) hPB
  refine ⟨hperm,?_⟩
  intro t htw hCt
  obtain ⟨Q,hQP,hQI,hcover⟩ := hdecomp t.toFinset hCt
  have in_union {S : Finset X} (hSQ : S ∈ Q) {x : X} (hxS : x ∈ S) : x ∈ t := by
    apply List.mem_toFinset.mp
    rw [hcover]
    exact Finset.mem_biUnion.mpr ⟨S,hSQ,hxS⟩
  have union_absent {x : X} (hx : x ∉ Q.biUnion id) : x ∉ t := by
    intro hxt
    exact hx (hcover ▸ List.mem_toFinset.mpr hxt)
  have hleftR (x : X) (hx : x ∈ U ++ [alpha,beta]) : x ∈ Ω \ insert q Blue := by
    rcases List.mem_append.mp hx with hx | hx
    · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hαR
      · have he : x = beta := by simpa using hx
        exact he.symm ▸ hβR
  have hrightB (x : X) (hx : x ∈ P ++ V) : x ∈ Blue := by
    rcases List.mem_append.mp hx with hx | hx
    · exact hPB x hx
    · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1
  by_cases hqt : q ∈ t
  · have hqA : q ∈ Q.biUnion id := hcover ▸ List.mem_toFinset.mpr hqt
    obtain ⟨d,hdQ,hqd⟩ := Finset.mem_biUnion.mp hqA
    have hdT : d ∈ neighborhood M Ω q := mem_neighborhood.mpr ⟨hQP hdQ,hqd⟩
    by_cases hda : d = a
    · have haQ : a ∈ Q := hda ▸ hdQ
      have hαt := in_union haQ hαa
      have hβnot : beta ∉ t := union_absent (forbidden_port G hQP hQI
        haQ (mem_terminalNeighbors.mp ha).1 hz haz.symm hb0 ha hβN)
      have hw : w = (U ++ [alpha]) ++ beta :: (q :: (P ++ V)) := by
        simp [w,cycleWord,U,V,List.append_assoc]
      exact hβnot (infix_crosses hn htw hw (by simp) (by simp) hαt hqt)
    · have hdmap : d ∈ (C.first :: C.tail).map Prod.fst := by
        apply List.mem_toFinset.mp
        rw [C.terminals_cover]
        exact hdT
      obtain ⟨f,hf,hfd⟩ := List.mem_map.mp hdmap
      have hft : f ∈ C.tail := by
        rcases List.mem_cons.mp hf with he | he
        · have hfirst : d = a := hfd.symm.trans
            ((congrArg Prod.fst he).trans C.first_terminal)
          exact (hda hfirst).elim
        · exact he
      obtain ⟨p,e,s,hsplit⟩ := predecessor (a := C.first) hft
      have heL : e ∈ C.first :: C.tail := by rw [hsplit]; simp
      have hpair : [e,f] <:+: C.first :: C.tail := by
        exact ⟨p,s,by simpa [List.append_assoc] using hsplit.symm⟩
      have hstep : PortStep G e f := List.isChain_pair.mp
        (C.steps.left_of_append.infix hpair)
      obtain ⟨b,hb,heN,hfb⟩ := hstep
      have hnd : ((p.map Prod.fst) ++ e.1 :: f.1 :: s.map Prod.fst).Nodup := by
        simpa only [hsplit,List.map_append,List.map_cons] using C.terminals_nodup
      have hnd' := (List.nodup_append.mp hnd).2.1
      have hef : e.1 ≠ f.1 := by
        intro he
        exact (List.nodup_cons.mp hnd').1 (by simp [he])
      have hed : e.1 ≠ d := fun he => hef (he.trans hfd.symm)
      have heAbsent : e.2 ∉ t := union_absent (forbidden_port G hQP hQI hdQ hdT
        (C.terminal_mem G heL) hed hb (hfd ▸ hfb) heN)
      obtain ⟨c,hc,hfN⟩ := C.port_incidence f hf
      have hfmem : f.2 ∈ d := by
        have hmem : f.1 ∈ neighborhood M Ω f.2 := by rw [hfN]; simp
        exact hfd ▸ (mem_neighborhood.mp hmem).2
      have hfPresent := in_union hdQ hfmem
      have hPsplit : P = p.map Prod.snd ++ e.2 :: f.2 :: s.map Prod.snd := by
        change (C.first :: C.tail).map Prod.snd = _
        rw [hsplit]
        simp only [List.map_append,List.map_cons]
      have hw : w = (U ++ [alpha,beta,q] ++ p.map Prod.snd) ++
          e.2 :: (f.2 :: (s.map Prod.snd ++ V)) := by
        change U ++ alpha :: beta :: q :: (P ++ V) = _
        rw [hPsplit]
        simp only [List.append_assoc,List.cons_append,List.nil_append]
      exact heAbsent (infix_crosses hn htw hw (by simp) (by simp) hqt hfPresent)
  · obtain ⟨x,hxA⟩ := hCt.2.1
    have hxU : x ∈ Q.biUnion id := hcover ▸ hxA
    obtain ⟨S,hSQ,hxS⟩ := Finset.mem_biUnion.mp hxU
    have hqS : q ∉ S := fun hqS => hqt (in_union hSQ hqS)
    obtain ⟨⟨r,hrS,hrR⟩,b,hbS,hbB⟩ := hmixed S (hQP hSQ) hqS
    have hrt := in_union hSQ hrS
    have hbt := in_union hSQ hbS
    have hw : w = (U ++ [alpha,beta]) ++ q :: (P ++ V) := by
      simp [w,cycleWord,U,V,List.append_assoc]
    have htw' : t <:+: (U ++ [alpha,beta]) ++ q :: (P ++ V) := hw ▸ htw
    rcases infix_avoid_separator htw' hqt with hL | hR
    · exact (Finset.mem_sdiff.mp (hleftR b (hL.subset hbt))).2
        (Finset.mem_insert_of_mem hbB)
    · exact (Finset.mem_sdiff.mp hrR).2
        (Finset.mem_insert_of_mem (hrightB r (hR.subset hrt)))

/-- Consumed native-colouring consequence. Everything local, including mixed B
stars and the actual red alpha/beta, is constructed above. `houtside` is only
the separate exterior mixed-colouring obligation; it includes private ports
as distinct original IDs. `hdecomp` ranges over ALL Complete rows.

The actual PortCycle is constructed by exists_portCycle, consuming the
Hamilton proof above and both endpoint rank bounds. The earlier positive-
geometry derivation and full original positiveGood are not asserted. Section
5a is a separate formalization obligation. -/
theorem native_avoiding_word (H : Finset (Finset X))
    (G : Geometry (originalSpan H) Ω q) (b0 a z u : Finset X)
    (rank : Finset X → ℕ) (hb0 : b0 ∈ G.B)
    (ha : a ∈ terminalNeighbors (originalSpan H) Ω q b0)
    (hz : z ∈ terminalNeighbors (originalSpan H) Ω q b0) (haz : a ≠ z)
    (hu : u ∈ neighborhood (originalSpan H) Ω q)
    (hu0 : u ∉ terminalNeighbors (originalSpan H) Ω q b0)
    (hrank : ∀ s ∈ neighborhood (originalSpan H) Ω q,
      ∀ t ∈ neighborhood (originalSpan H) Ω q,
      rank s = rank t → s = t)
    (hmin : ∀ t ∈ neighborhood (originalSpan H) Ω q, rank a ≤ rank t)
    (hmax : ∀ t ∈ neighborhood (originalSpan H) Ω q, rank t ≤ rank z)
    {K : Finset X} (hK : K ⊆ Ω.erase q)
    (hKB : ∀ b ∈ G.B, Disjoint K b)
    (houtside : ∀ S ∈ minimalFamily (originalSpan H) Ω, q ∉ S → S ∉ G.B →
      (∃ x ∈ S, x ∈ red G b0 z rank K) ∧
        (∃ y ∈ S, y ∈ blue G b0 z rank K))
    (hdecomp : ∀ A, Complete (originalSpan H) Ω A →
      ∃ Q : Finset (Finset X), Q ⊆ minimalFamily (originalSpan H) Ω ∧ Independent Q ∧
        A = Q.biUnion id) :
    ∃ (C : PortCycle G (blue G b0 z rank K) a) (alpha beta : X),
      alpha ∈ a ∧ alpha ∈ red G b0 z rank K ∧ beta ∈ red G b0 z rank K ∧
      alpha ≠ beta ∧
      let P := (C.first :: C.tail).map Prod.snd
      let w := cycleWord Ω (blue G b0 z rank K) q alpha beta P
      w.Perm Ω.toList ∧ ∀ t : List X, t <:+: w →
        ¬Complete (originalSpan H) Ω t.toFinset := by
  obtain ⟨C⟩ := exists_portCycle G b0 a z u rank hb0 ha hz haz hu hu0
    hrank hmin hmax hKB
  obtain ⟨alpha,beta,hαa,hαR,hβR,hαβ,hβN⟩ :=
    red_frame G b0 a z u rank hb0 ha hz haz hu hu0 hmin hKB
  refine ⟨C,alpha,beta,hαa,hαR,hβR,hαβ,?_⟩
  apply avoiding_word_of_portCycle G (blue_subset G b0 z rank hK) hb0 ha
    (mem_terminalNeighbors.mp hz).1 haz C hαa hαR hβR hαβ hβN
  · intro S hSP hqS
    by_cases hSB : S ∈ G.B
    · exact mixed_B G b0 z rank hz hrank hKB hSB
    · exact houtside S hSP hqS hSB
  · exact hdecomp

end D5.S3.Combinatorics.Sequenceability.PositiveChargePorts
