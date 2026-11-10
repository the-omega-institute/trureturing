/- GID: D5/S3/Combinatorics/Sequenceability/PositiveChargePortGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PositiveChargePortGeometry
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original port colours give connected semicomplete terminal geometry and row separation. -/

import D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent

/-! Original-coordinate port incidence, ranked colours and terminal paths. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.Sequenceability.PositiveChargePorts
open Finset
open scoped Classical
open D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
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

end D5.S3.Combinatorics.Sequenceability.PositiveChargePorts
