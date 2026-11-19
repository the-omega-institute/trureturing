/- GID: D5/S3/Quantum/Tomography/MUB/BoundarySphereCover
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUB/BoundarySphereCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Tomography/MUB/BoundarySphereCover.sphereCovered; instance=D5/S3/Quantum/Tomography/MUB/BoundarySphereCover.actual_2762_certificate
   digest: Directed ridge certificates imply four-dimensional spherical cap coverage. -/

import Lean
import Std

/-! Every accepted directed-ridge certificate covers a four-dimensional sphere.
The maximizing dual gives nonnegative basis coordinates without assuming a complete fan. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUB.BoundarySphereCover


namespace S3Cover
abbrev V4 := Int × Int × Int × Int
abbrev I4 := Nat × Nat × Nat × Nat

structure Cap where
  v : V4
  h : Int
  deriving Repr

structure Facet where
  idx : I4
  num : V4
  den : Int
  deriving Repr

def dot (x y : V4) : Int :=
  x.1*y.1 + x.2.1*y.2.1 + x.2.2.1*y.2.2.1 + x.2.2.2*y.2.2.2

def det3 (a b c d e f g h i : Int) : Int :=
  a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)

def det4 (x y z w : V4) : Int :=
  x.1 * det3 y.2.1 y.2.2.1 y.2.2.2 z.2.1 z.2.2.1 z.2.2.2 w.2.1 w.2.2.1 w.2.2.2 -
  x.2.1 * det3 y.1 y.2.2.1 y.2.2.2 z.1 z.2.2.1 z.2.2.2 w.1 w.2.2.1 w.2.2.2 +
  x.2.2.1 * det3 y.1 y.2.1 y.2.2.2 z.1 z.2.1 z.2.2.2 w.1 w.2.1 w.2.2.2 -
  x.2.2.2 * det3 y.1 y.2.1 y.2.2.1 z.1 z.2.1 z.2.2.1 w.1 w.2.1 w.2.2.1

def I4.nodes (p : I4) : List Nat := [p.1, p.2.1, p.2.2.1, p.2.2.2]
def I4.ridges (p : I4) : List (List Nat) :=
  [[p.2.1,p.2.2.1,p.2.2.2], [p.1,p.2.2.1,p.2.2.2],
   [p.1,p.2.1,p.2.2.2], [p.1,p.2.1,p.2.2.1]]

def validCap (c : Cap) : Bool := decide (0 < c.h ∧ c.h*c.h < dot c.v c.v)

def supports (f : Facet) (i : Nat) (c : Cap) : Bool :=
  if f.idx.nodes.contains i then decide (dot c.v f.num = c.h*f.den)
  else decide (dot c.v f.num < c.h*f.den)

def validFacet (caps : List Cap) (f : Facet) : Bool :=
  let p := f.idx
  match caps[p.1]?, caps[p.2.1]?, caps[p.2.2.1]?, caps[p.2.2.2]? with
  | some a, some b, some c, some d =>
    decide (p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2 ∧
      det4 a.v b.v c.v d.v ≠ 0 ∧ 0 < f.den ∧ dot f.num f.num ≤ f.den*f.den) &&
    (caps.zipIdx).all (fun (x,i) => supports f i x)
  | _,_,_,_ => false

def paired (all : List Facet) (f : Facet) : Bool :=
  f.idx.ridges.all (fun ridge =>
    (all.filter (fun g => g.idx.ridges.contains ridge)).length == 2)

def adjacent (all : List Facet) (f : Facet) : Bool :=
  f.idx.ridges.all (fun ridge =>
    all.any (fun g => g.idx.nodes != f.idx.nodes && g.idx.ridges.contains ridge))

def directed (all : List Facet) (f : Facet) : Bool :=
  f.idx.nodes.all (fun u =>
    all.any (fun g => !(g.idx.nodes.contains u) &&
      (f.idx.nodes.filter (· != u)).all g.idx.nodes.contains))

def certificate (caps : List Cap) (faces : List Facet) : Bool :=
  !faces.isEmpty && caps.all validCap &&
    decide ((faces.map (fun f => f.idx.nodes)).Nodup) &&
    faces.all (fun f => ((validFacet caps f && paired faces f) && adjacent faces f) && directed faces f)

theorem certificate_nonempty {caps : List Cap} {faces : List Facet}
    (h : certificate caps faces = true) : faces ≠ [] := by
  intro he
  subst faces
  simp [certificate] at h

theorem certificate_caps {caps : List Cap} {faces : List Facet}
    (h : certificate caps faces = true) (c : Cap) (hc : c ∈ caps) :
    0 < c.h ∧ c.h*c.h < dot c.v c.v := by
  simp only [certificate, Bool.and_eq_true] at h
  have he := List.all_eq_true.mp h.1.1.2 c hc
  exact of_decide_eq_true he

theorem certificate_face {caps : List Cap} {faces : List Facet}
    (h : certificate caps faces = true) (f : Facet) (hf : f ∈ faces) :
    validFacet caps f = true ∧ paired faces f = true ∧ adjacent faces f = true ∧ directed faces f = true := by
  simp only [certificate, Bool.and_eq_true] at h
  simpa only [Bool.and_eq_true, and_assoc] using List.all_eq_true.mp h.2 f hf

theorem certificate_adjacent {caps : List Cap} {faces : List Facet}
    (h : certificate caps faces = true) (f : Facet) (hf : f ∈ faces)
    (r : List Nat) (hr : r ∈ f.idx.ridges) :
    ∃ g ∈ faces, g.idx.nodes ≠ f.idx.nodes ∧ r ∈ g.idx.ridges := by
  have he := List.all_eq_true.mp (certificate_face h f hf).2.2.1 r hr
  obtain ⟨g, hg, he'⟩ := List.any_eq_true.mp he
  simp only [Bool.and_eq_true, bne_iff_ne, List.contains_iff_mem] at he'
  exact ⟨g, hg, he'⟩

theorem facet_values {caps : List Cap} {f : Facet} (h : validFacet caps f = true) :
    0 < f.den ∧ dot f.num f.num ≤ f.den*f.den ∧
    ∃ a b c d : Cap,
      caps[f.idx.1]? = some a ∧ caps[f.idx.2.1]? = some b ∧
      caps[f.idx.2.2.1]? = some c ∧ caps[f.idx.2.2.2]? = some d ∧
      det4 a.v b.v c.v d.v ≠ 0 := by
  unfold validFacet at h
  dsimp only at h
  split at h
  next a b c d ha hb hc hd =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.2.2.2.2.1, h.1.2.2.2.2.2, a,b,c,d,ha,hb,hc,hd,h.1.2.2.2.1⟩
  next => contradiction

theorem facet_support {caps : List Cap} {f : Facet} (h : validFacet caps f = true)
    (i : Nat) (c : Cap) (hc : (c,i) ∈ caps.zipIdx) :
    if i ∈ f.idx.nodes then dot c.v f.num = c.h * f.den
    else dot c.v f.num < c.h * f.den := by
  unfold validFacet at h
  dsimp only at h
  split at h
  next a b c' d ha hb hc' hd =>
    simp only [Bool.and_eq_true] at h
    have hs := List.all_eq_true.mp h.2 (c,i) hc
    by_cases hi : i ∈ f.idx.nodes
    · simpa [supports, List.contains_iff_mem, hi] using hs
    · simpa [supports, List.contains_iff_mem, hi] using hs
  next => contradiction

/-- A valid certificate contains an explicit usable directed ridge neighbor,
not merely a count of distinct facets. -/
theorem certificate_directed {caps : List Cap} {faces : List Facet}
    (h : certificate caps faces = true) (f : Facet) (hf : f ∈ faces)
    (u : Nat) (hu : u ∈ f.idx.nodes) :
    ∃ g ∈ faces, u ∉ g.idx.nodes ∧ ∀ v ∈ f.idx.nodes, v ≠ u → v ∈ g.idx.nodes := by
  have he := List.all_eq_true.mp (certificate_face h f hf).2.2.2 u hu
  obtain ⟨g, hg, he'⟩ := List.any_eq_true.mp he
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at he'
  refine ⟨g, hg, ?_, ?_⟩
  · intro hm
    have hh : g.idx.nodes.contains u = true := List.contains_iff_mem.mpr hm
    exact Bool.noConfusion (he'.1.symm.trans hh)
  · intro v hv hn
    have hm : v ∈ f.idx.nodes.filter (· != u) := List.mem_filter.mpr ⟨hv, bne_iff_ne.mpr hn⟩
    exact List.contains_iff_mem.mp (List.all_eq_true.mp he'.2 v hm)

theorem certificate_directed_strict {caps : List Cap} {faces : List Facet}
    (h : certificate caps faces = true) (f : Facet) (hf : f ∈ faces)
    (u : Nat) (c : Cap) (hu : u ∈ f.idx.nodes) (huc : (c,u) ∈ caps.zipIdx) :
    ∃ g ∈ faces,
      dot c.v g.num < c.h*g.den ∧
      ∀ v d, v ∈ f.idx.nodes → v ≠ u → (d,v) ∈ caps.zipIdx →
        dot d.v g.num = d.h*g.den := by
  obtain ⟨g, hg, hu', hrest⟩ := certificate_directed h f hf u hu
  have hv := (certificate_face h g hg).1
  refine ⟨g, hg, ?_, ?_⟩
  · simpa only [ite_eq_right hu'] using facet_support hv u c huc
  · intro v d hv' hne hdc
    simpa only [ite_eq_left (hrest v hv' hne)] using facet_support hv v d hdc

def index4 (p : I4) (i : Fin 4) : Nat :=
  match i.val with
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2.1
  | _ => p.2.2.2

theorem four_cases {P : Fin 4 → Prop} (h₀ : P 0) (h₁ : P 1) (h₂ : P 2) (h₃ : P 3) :
    ∀ i, P i
  | ⟨0, _⟩ => h₀
  | ⟨1, _⟩ => h₁
  | ⟨2, _⟩ => h₂
  | ⟨3, _⟩ => h₃

theorem index4_mem (p : I4) (i : Fin 4) : index4 p i ∈ p.nodes :=
  four_cases (P := fun k => index4 p k ∈ p.nodes) (by simp [index4, I4.nodes]) (by simp [index4, I4.nodes])
    (by simp [index4, I4.nodes]) (by simp [index4, I4.nodes]) i

theorem validFacet_ordered {caps : List Cap} {f : Facet} (h : validFacet caps f = true) :
    f.idx.1 < f.idx.2.1 ∧ f.idx.2.1 < f.idx.2.2.1 ∧ f.idx.2.2.1 < f.idx.2.2.2 := by
  unfold validFacet at h
  dsimp only at h
  split at h
  next =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩
  next => contradiction

theorem index4_inj {p : I4}
    (h : p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2) :
    ∀ {i j}, index4 p i = index4 p j → i = j := by
  intro i j
  revert i j
  apply four_cases <;> apply four_cases <;> simp [index4] <;> omega

def capAt (caps : List Cap) (j : Nat) : Cap := caps[j]?.getD ⟨(0,0,0,0), 1⟩

theorem index4_get {caps : List Cap} {f : Facet} (h : validFacet caps f = true)
    (k : Fin 4) :
    (capAt caps (index4 f.idx k), index4 f.idx k) ∈ caps.zipIdx := by
  obtain ⟨_,_,a,b,c,d,ha,hb,hc,hd,_⟩ := facet_values h
  apply four_cases (P := fun k => (capAt caps (index4 f.idx k), index4 f.idx k) ∈ caps.zipIdx)
  · simp [capAt, index4, List.mk_mem_zipIdx_iff_getElem?, ha]
  · simp [capAt, index4, List.mk_mem_zipIdx_iff_getElem?, hb]
  · simp [capAt, index4, List.mk_mem_zipIdx_iff_getElem?, hc]
  · simp [capAt, index4, List.mk_mem_zipIdx_iff_getElem?, hd]

end S3Cover


/-! Finite dual maximization proves cone coverage and then cap coverage.
No topology, fan assumptions, or Mathlib are needed in this carrier-agnostic
proof. Replace the ordinary ordered-arithmetic laws by their standard
real instances when consuming a real-valued dual certificate. -/

namespace MUB.DualGreedy

variable {R ι V X : Type} [LE R] [LT R] [OfNat R 0] [OfNat R 1] [Add R] [Mul R]

structure OrderedWeightLaws (R : Type) [LE R] [LT R] [OfNat R 0] [OfNat R 1]
    [Add R] [Mul R] : Prop where
  leRefl : ∀ a : R, a ≤ a
  leTrans : ∀ {a b c : R}, a ≤ b → b ≤ c → a ≤ c
  leTotal : ∀ a b : R, a ≤ b ∨ b ≤ a
  nlt : ∀ {a b : R}, a ≤ b → ¬ b < a
  notLe : ∀ {a b : R}, (¬ a ≤ b) → b < a
  ltTransLe : ∀ {a b c : R}, a < b → b ≤ c → a < c
  ltTrans : ∀ {a b c : R}, a < b → b < c → a < c
  zeroLtOne : (0:R) < 1
  mulZero : ∀ a : R, (0:R) * a = 0
  zeroAdd : ∀ a : R, 0 + a = a
  mulOne : ∀ a : R, a * 1 = a
  mulLe : ∀ {a b c : R}, 0 ≤ a → b ≤ c → a * b ≤ a * c
  mulLt : ∀ {a b c : R}, 0 < a → b < c → a * b < a * c
  mulLtNeg : ∀ {a b c : R}, a < 0 → b < c → a * c < a * b
  leAddLe : ∀ {a b c d : R}, a ≤ b → c ≤ d → a+c ≤ b+d
  leAddLt : ∀ {a b c d : R}, a ≤ b → c < d → a+c < b+d
  ltAddLe : ∀ {a b c d : R}, a < b → c ≤ d → a+c < b+d
  notLt : ∀ {a b : R}, (¬ a < b) → b ≤ a
  eqOfLe : ∀ {a b : R}, a ≤ b → b ≤ a → a = b

private theorem maximum_on_list (L : OrderedWeightLaws R)
    (f : ι → R) (x : ι) (xs : List ι) :
    ∃ i ∈ x :: xs, ∀ j ∈ x :: xs, f j ≤ f i := by
  induction xs generalizing x with
  | nil =>
    refine ⟨x, List.mem_cons_self, ?_⟩
    intro j h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst j
    exact L.leRefl _
  | cons y ys ih =>
    obtain ⟨i, hi, hmax⟩ := ih y
    rcases L.leTotal (f x) (f i) with hx | hx
    · refine ⟨i, List.mem_cons_of_mem _ hi, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hx
      · exact hmax j hj
    · refine ⟨x, List.mem_cons_self, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact L.leRefl _
      · exact L.leTrans (hmax j hj) hx

def weighted (vs : List V) (coeff value : V → R) : R :=
  vs.foldr (fun v s => coeff v * value v + s) 0

private theorem weighted_zero (L : OrderedWeightLaws R)
    (vs : List V) (coeff value : V → R)
    (hzero : ∀ v ∈ vs, coeff v = 0) :
    weighted vs coeff value = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    unfold weighted at *
    simp only [List.foldr_cons]
    rw [hzero v List.mem_cons_self, L.mulZero, L.zeroAdd,
      ih (fun w hw => hzero w (List.mem_cons_of_mem _ hw))]

private theorem weighted_le (L : OrderedWeightLaws R)
    (vs : List V) (coeff value value' : V → R)
    (hcoeff : ∀ v ∈ vs, 0 ≤ coeff v)
    (hle : ∀ v ∈ vs, value v ≤ value' v) :
    weighted vs coeff value ≤ weighted vs coeff value' := by
  induction vs with
  | nil => exact L.leRefl _
  | cons v vs ih =>
    apply L.leAddLe
    · exact L.mulLe (hcoeff v List.mem_cons_self) (hle v List.mem_cons_self)
    · exact ih (fun w hw => hcoeff w (List.mem_cons_of_mem _ hw))
        (fun w hw => hle w (List.mem_cons_of_mem _ hw))

private theorem weighted_lt (L : OrderedWeightLaws R)
    (vs : List V) (coeff value value' : V → R)
    (hcoeff : ∀ v ∈ vs, 0 ≤ coeff v)
    (hle : ∀ v ∈ vs, value v ≤ value' v)
    (i : V) (hi : i ∈ vs) (hci : 0 < coeff i) (hli : value i < value' i) :
    weighted vs coeff value < weighted vs coeff value' := by
  induction vs with
  | nil => contradiction
  | cons v vs ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · apply L.ltAddLe (L.mulLt hci hli)
      exact weighted_le L vs _ _ _ (fun w hw => hcoeff w (List.mem_cons_of_mem _ hw))
        (fun w hw => hle w (List.mem_cons_of_mem _ hw))
    · apply L.leAddLt (L.mulLe (hcoeff v List.mem_cons_self) (hle v List.mem_cons_self))
      exact ih (fun w hw => hcoeff w (List.mem_cons_of_mem _ hw))
        (fun w hw => hle w (List.mem_cons_of_mem _ hw)) hi

private theorem weighted_le_pointwise (L : OrderedWeightLaws R)
    (vs : List V) (coeff value value' : V → R)
    (hle : ∀ v ∈ vs, coeff v * value v ≤ coeff v * value' v) :
    weighted vs coeff value ≤ weighted vs coeff value' := by
  induction vs with
  | nil => exact L.leRefl _
  | cons v vs ih =>
    apply L.leAddLe (hle v List.mem_cons_self)
    exact ih (fun w hw => hle w (List.mem_cons_of_mem _ hw))

private theorem weighted_lt_pointwise (L : OrderedWeightLaws R)
    (vs : List V) (coeff value value' : V → R)
    (hle : ∀ v ∈ vs, coeff v * value v ≤ coeff v * value' v)
    (i : V) (hi : i ∈ vs)
    (hi' : coeff i * value i < coeff i * value' i) :
    weighted vs coeff value < weighted vs coeff value' := by
  induction vs with
  | nil => contradiction
  | cons v vs ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · apply L.ltAddLe hi'
      exact weighted_le_pointwise L vs _ _ _ (fun w hw => hle w (List.mem_cons_of_mem _ hw))
    · apply L.leAddLt (hle v List.mem_cons_self)
      exact ih (fun w hw => hle w (List.mem_cons_of_mem _ hw)) hi

/-- Greedy closure. The local inequality is exactly the positivity of the ridge step:
if local coefficient v is negative, the stored neighboring facet has strictly greater
objective. Only one directed neighbor per omitted vertex is necessary. -/
theorem exists_nonnegative_chart (L : OrderedWeightLaws R)
    (head : ι) (tail : List ι) (vertices : ι → List V)
    (score : ι → R) (coeff : ι → V → R)
    (ridge : ∀ i ∈ head :: tail, ∀ v ∈ vertices i, coeff i v < 0 →
      ∃ j ∈ head :: tail, score i < score j) :
    ∃ i ∈ head :: tail, ∀ v ∈ vertices i, 0 ≤ coeff i v := by
  obtain ⟨i, hi, hmax⟩ := maximum_on_list L score head tail
  refine ⟨i, hi, ?_⟩
  intro v hv
  apply Classical.byContradiction
  intro hn
  obtain ⟨j, hj, hstep⟩ := ridge i hi v hv (L.notLe hn)
  exact L.nlt (hmax j hj) hstep

/-- A certificate plus the four-vector reconstruction identities yields a
closed-cap cover. The hypothesis `hbound` is immediate for unit input by
Cauchy–Schwarz because each dual vector has norm ≤ 1. -/
theorem exists_cap (L : OrderedWeightLaws R)
    (head : ι) (tail : List ι) (vertices : ι → List V)
    (score : ι → R) (coeff : ι → V → R) (test : V → R)
    (ridge : ∀ i ∈ head :: tail, ∀ v ∈ vertices i, coeff i v < 0 →
      ∃ j ∈ head :: tail, score i < score j)
    (hmass : ∀ i ∈ head :: tail, weighted (vertices i) (coeff i) (fun _ => 1) = score i)
    (htest : ∀ i ∈ head :: tail, weighted (vertices i) (coeff i) test = 1)
    (hbound : ∀ i ∈ head :: tail, score i ≤ 1) :
    ∃ i ∈ head :: tail, ∃ v ∈ vertices i, 1 ≤ test v := by
  obtain ⟨i, hi, hcoeff⟩ := exists_nonnegative_chart L head tail vertices score coeff ridge
  have hpositive : ∃ v ∈ vertices i, 0 < coeff i v := by
    apply Classical.byContradiction
    intro hn
    have hz v (hv : v ∈ vertices i) : coeff i v = 0 := by
      have hnot : ¬ (0:R) < coeff i v := fun hh => hn ⟨v,hv,hh⟩
      exact L.eqOfLe (L.notLt hnot) (hcoeff v hv)
    have he := weighted_zero L (vertices i) (coeff i) test hz
    rw [htest i hi] at he
    exact L.nlt (L.leRefl (0:R)) (he ▸ L.zeroLtOne)
  obtain ⟨v, hv, hp⟩ := hpositive
  refine ⟨i, hi, ?_⟩
  apply Classical.byContradiction
  intro hn
  have hs w (hw : w ∈ vertices i) : test w < 1 :=
    L.notLe (fun hh => hn ⟨w,hw,hh⟩)
  have hle w (hw : w ∈ vertices i) : test w ≤ 1 := by
    apply Classical.byContradiction
    intro e
    exact L.nlt (L.leRefl _) (L.ltTrans (hs w hw) (L.notLe e))
  have hh := weighted_lt L (vertices i) (coeff i) test (fun _ => 1)
    hcoeff hle v hv hp (hs v hv)
  rw [htest i hi, hmass i hi] at hh
  exact L.nlt (hbound i hi) hh

/-- Topology-free collapse from a list of full-rank dual charts to a cap cover.
For the fixed unit direction, `coeff i` are its coefficients in chart `i`,
`score j` is its scalar product with the dual vector of chart `j`,
`support j v` is the scalar product of that dual vector with generator `v`,
and `test v` is the scalar product of direction and generator `v`.
The two reconstruction hypotheses express bilinearity. A neighboring chart
need only support all other vertices at 1 and the omitted vertex below 1. -/
theorem exists_cap_of_directed_ridges (L : OrderedWeightLaws R)
    (head : ι) (tail : List ι) (vertices : ι → List V)
    (score : ι → R) (coeff support : ι → V → R) (test : V → R)
    (hdiag : ∀ i ∈ head :: tail, ∀ v ∈ vertices i, support i v = 1)
    (hdual : ∀ i ∈ head :: tail, ∀ j ∈ head :: tail,
      weighted (vertices i) (coeff i) (support j) = score j)
    (hridge : ∀ i ∈ head :: tail, ∀ u ∈ vertices i,
      ∃ j ∈ head :: tail, support j u < 1 ∧
        ∀ v ∈ vertices i, v ≠ u → support j v = 1)
    (htest : ∀ i ∈ head :: tail, weighted (vertices i) (coeff i) test = 1)
    (hbound : ∀ i ∈ head :: tail, score i ≤ 1) :
    ∃ i ∈ head :: tail, ∃ v ∈ vertices i, 1 ≤ test v := by
  classical
  apply exists_cap L head tail vertices score coeff test _ _ htest hbound
  · intro i hi u hu hneg
    obtain ⟨j,hj,hlt,heq⟩ := hridge i hi u hu
    refine ⟨j,hj,?_⟩
    rw [← hdual i hi i hi, ← hdual i hi j hj]
    apply weighted_lt_pointwise L _ _ _ _ _ u hu
    · rw [hdiag i hi u hu]
      exact L.mulLtNeg hneg hlt
    · intro v hv
      rw [hdiag i hi v hv]
      by_cases h : v = u
      · subst v
        apply Classical.byContradiction
        intro hn
        exact L.nlt (L.leRefl _) (L.ltTrans (L.mulLtNeg hneg hlt) (L.notLe hn))
      · rw [heq v hv h]
        exact L.leRefl _
  · intro i hi
    rw [← hdual i hi i hi]
    apply L.eqOfLe <;> apply weighted_le_pointwise L <;> intro v hv <;>
      rw [hdiag i hi v hv] <;> exact L.leRefl _

end MUB.DualGreedy


namespace MUB.DualGreedy
open Lean.Grind Std

variable {R : Type} [CommRing R] [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R]
  [OrderedRing R]

theorem stdWeightLaws : OrderedWeightLaws R where
  leRefl := le_refl
  leTrans := le_trans
  leTotal := fun _ _ => le_total
  nlt := by grind
  notLe := by grind
  ltTransLe := by grind
  ltTrans := by grind
  zeroLtOne := OrderedRing.zero_lt_one
  mulZero := Semiring.zero_mul
  zeroAdd := AddCommMonoid.zero_add
  mulOne := Semiring.mul_one
  mulLe h₁ h₂ := OrderedRing.mul_le_mul_of_nonneg_left h₂ h₁
  mulLt h₁ h₂ := OrderedRing.mul_lt_mul_of_pos_left h₂ h₁
  mulLtNeg h₁ h₂ := OrderedRing.mul_lt_mul_of_neg_left h₂ h₁
  leAddLe := OrderedAdd.add_le_add
  leAddLt := by grind
  ltAddLe := by grind
  notLt := by grind
  eqOfLe := le_antisymm

abbrev Vec4 (R : Type) := Fin 4 → R

def sum4 (f : Fin 4 → R) : R :=
  f 0 + (f 1 + (f 2 + (f 3 + 0)))

def dot4 (x y : Vec4 R) : R := sum4 (fun i => x i * y i)

theorem dot_le_one_of_normsq (x y : Vec4 R)
    (hx : dot4 x x = 1) (hy : dot4 y y ≤ 1) :
    dot4 x y ≤ 1 := by
  have sq₀ : 0 ≤ (x 0 - y 0) * (x 0 - y 0) := by
    simpa only [Semiring.pow_two] using (OrderedRing.sq_nonneg (a := x 0 - y 0))
  have sq₁ : 0 ≤ (x 1 - y 1) * (x 1 - y 1) := by
    simpa only [Semiring.pow_two] using (OrderedRing.sq_nonneg (a := x 1 - y 1))
  have sq₂ : 0 ≤ (x 2 - y 2) * (x 2 - y 2) := by
    simpa only [Semiring.pow_two] using (OrderedRing.sq_nonneg (a := x 2 - y 2))
  have sq₃ : 0 ≤ (x 3 - y 3) * (x 3 - y 3) := by
    simpa only [Semiring.pow_two] using (OrderedRing.sq_nonneg (a := x 3 - y 3))
  have e : (x 0 - y 0) * (x 0 - y 0) + (x 1 - y 1) * (x 1 - y 1) +
       (x 2 - y 2) * (x 2 - y 2) + (x 3 - y 3) * (x 3 - y 3) =
      dot4 x x + dot4 y y - dot4 x y - dot4 x y := by
    unfold dot4 sum4
    grind
  grind

variable {I V : Type}

def reconstruct (q : V → Vec4 R) (faces : I → Fin 4 → V)
    (coeff : I → Fin 4 → R) (i : I) : Vec4 R :=
  fun s => sum4 (fun j => coeff i j * q (faces i j) s)

omit [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R] in
private theorem dot4_reconstruct (q : V → Vec4 R) (faces : I → Fin 4 → V)
    (coeff : I → Fin 4 → R) (i : I) (y : Vec4 R) :
    weighted ([0,1,2,3] : List (Fin 4)) (coeff i)
        (fun k => dot4 (q (faces i k)) y) =
    dot4 (reconstruct q faces coeff i) y := by
  unfold weighted dot4 reconstruct sum4
  simp only [List.foldr_cons, List.foldr_nil]
  grind

omit [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R] in
theorem dot4_comm (x y : Vec4 R) : dot4 x y = dot4 y x := by
  unfold dot4 sum4
  grind

private theorem four_mem (j : Fin 4) : j ∈ ([0,1,2,3] : List (Fin 4)) := by
  match j with
  | ⟨0,_⟩ => simp
  | ⟨1,_⟩ => simp
  | ⟨2,_⟩ => simp
  | ⟨3,_⟩ => simp

/-- Algebraic support-to-cap theorem for a fixed unit direction. The coefficients
are the basis-expansion coordinates; an inverse matrix computes them. -/
theorem vec4_cap_of_directed_ridges
    (head : I) (tail : List I) (q : V → Vec4 R)
    (faces : I → Fin 4 → V) (dual : I → Vec4 R) (x : Vec4 R)
    (coeff : I → Fin 4 → R)
    (hx : dot4 x x = 1)
    (hInv : ∀ i ∈ head :: tail, reconstruct q faces coeff i = x)
    (hNorm : ∀ i ∈ head :: tail, dot4 (dual i) (dual i) ≤ 1)
    (hExactly : ∀ i ∈ head :: tail, ∀ k, dot4 (q (faces i k)) (dual i) = 1)
    (hAdjacent : ∀ i ∈ head :: tail, ∀ k, ∃ j ∈ head :: tail,
      dot4 (q (faces i k)) (dual j) < 1 ∧
      ∀ l, l ≠ k → dot4 (q (faces i l)) (dual j) = 1) :
    ∃ i ∈ head :: tail, ∃ k : Fin 4, 1 ≤ dot4 (q (faces i k)) x := by
  let vertices (i : I) : List (I × Fin 4) := [(i,0),(i,1),(i,2),(i,3)]
  let support (j : I) (v : I × Fin 4) := dot4 (q (faces v.1 v.2)) (dual j)
  let test (v : I × Fin 4) := dot4 (q (faces v.1 v.2)) x
  let c (i : I) (v : I × Fin 4) := coeff i v.2
  have first (i : I) (v : I × Fin 4) (hv : v ∈ vertices i) : v.1 = i := by
    simp only [vertices, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h|h|h|h <;> rw [h]
  obtain ⟨i,hi,v,hv,hv'⟩ := exists_cap_of_directed_ridges
    stdWeightLaws head tail vertices (fun j => dot4 x (dual j)) c support test
    (by
      intro i hi v hv
      dsimp only [support]
      rw [first i v hv]
      exact hExactly i hi v.2)
    (by
      intro i hi j _
      change (weighted ([0,1,2,3] : List (Fin 4)) (coeff i) (fun k => dot4 (q (faces i k)) (dual j))) = _
      rw [dot4_reconstruct, hInv i hi])
    (by
      intro i hi u hu
      obtain ⟨j,hj,has,hes⟩ := hAdjacent i hi u.2
      refine ⟨j,hj,?_,?_⟩
      · dsimp only [support]
        rw [first i u hu]
        exact has
      · intro v hv hne
        dsimp only [support]
        rw [first i v hv]
        apply hes
        intro hh
        apply hne
        exact Prod.ext ((first i v hv).trans (first i u hu).symm) hh)
    (by
      intro i hi
      change (weighted ([0,1,2,3] : List (Fin 4)) (coeff i) (fun k => dot4 (q (faces i k)) x)) = _
      rw [dot4_reconstruct, hInv i hi, hx])
    (fun i hi => dot_le_one_of_normsq x (dual i) hx (hNorm i hi))
  refine ⟨i,hi,v.2,?_⟩
  change (1:R) ≤ dot4 (q (faces v.1 v.2)) x at hv'
  simpa only [first i v hv] using hv'

end MUB.DualGreedy


namespace MUB.DualGreedy
open Lean.Grind Std
variable {R : Type} [Field R]

def det3 (a b c d e f g h i : R) : R :=
  a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)

def det4 (u v w t : Vec4 R) : R :=
  u 0 * det3 (v 1) (v 2) (v 3) (w 1) (w 2) (w 3) (t 1) (t 2) (t 3) -
  u 1 * det3 (v 0) (v 2) (v 3) (w 0) (w 2) (w 3) (t 0) (t 2) (t 3) +
  u 2 * det3 (v 0) (v 1) (v 3) (w 0) (w 1) (w 3) (t 0) (t 1) (t 3) -
  u 3 * det3 (v 0) (v 1) (v 2) (w 0) (w 1) (w 2) (t 0) (t 1) (t 2)

def numerator (u v w t x : Vec4 R) (k : Fin 4) : R :=
  match k with
  | ⟨0,_⟩ => det4 x v w t
  | ⟨1,_⟩ => det4 u x w t
  | ⟨2,_⟩ => det4 u v x t
  | ⟨3,_⟩ => det4 u v w x

private theorem cramerNumerators (u v w t x : Vec4 R) (k : Fin 4) :
    det4 x v w t * u k + det4 u x w t * v k + det4 u v x t * w k + det4 u v w x * t k =
    x k * det4 u v w t := by
  match k with
  | ⟨0,_⟩ =>
    simp only [det4, det3]
    grind
  | ⟨1,_⟩ =>
    simp only [det4, det3]
    grind
  | ⟨2,_⟩ =>
    simp only [det4, det3]
    grind
  | ⟨3,_⟩ =>
    simp only [det4, det3]
    grind

/-- Cramer's theorem in the exact dimension needed by the archive. -/
theorem reconstruct_of_det_ne_zero (p : Fin 4 → Vec4 R) (x : Vec4 R)
    (hdet : det4 (p 0) (p 1) (p 2) (p 3) ≠ 0) :
    ∃ coeff : Fin 4 → R, ∀ s,
      sum4 (fun j => coeff j * p j s) = x s := by
  refine ⟨fun k => numerator (p 0) (p 1) (p 2) (p 3) x k / det4 (p 0) (p 1) (p 2) (p 3), ?_⟩
  intro s
  have e (a b c d u v w t z : R) :
      a / z * u + (b / z * v + (c / z * w + (d / z * t + 0))) =
      (a*u+b*v+c*w+d*t)/z := by
    simp only [Field.div_eq_mul_inv]
    grind
  change
      det4 x (p 1) (p 2) (p 3) / det4 (p 0) (p 1) (p 2) (p 3) * p 0 s +
      (det4 (p 0) x (p 2) (p 3) / det4 (p 0) (p 1) (p 2) (p 3) * p 1 s +
      (det4 (p 0) (p 1) x (p 3) / det4 (p 0) (p 1) (p 2) (p 3) * p 2 s +
      (det4 (p 0) (p 1) (p 2) x / det4 (p 0) (p 1) (p 2) (p 3) * p 3 s + 0))) = _
  rw [e, cramerNumerators]
  rw [← Field.div_mul]
  exact Field.div_mul_cancel hdet

/-- Multiplying each coefficient by its cap height changes the unnormalized
normal basis to the scaled basis without a second rank calculation. -/
theorem reconstruct_div_height_of_det_ne_zero
    (p : Fin 4 → Vec4 R) (height : Fin 4 → R) (x : Vec4 R)
    (hheight : ∀ j, height j ≠ 0)
    (hdet : det4 (p 0) (p 1) (p 2) (p 3) ≠ 0) :
    ∃ coeff : Fin 4 → R, ∀ s,
      sum4 (fun j => coeff j * (p j s / height j)) = x s := by
  obtain ⟨c,hc⟩ := reconstruct_of_det_ne_zero p x hdet
  refine ⟨fun j => c j * height j, ?_⟩
  intro s
  have he : (fun j => (c j * height j) * (p j s / height j)) =
      (fun j => c j * p j s) := by
    funext j
    have h := Field.div_mul_cancel (x := p j s) (hheight j)
    grind
  rw [he, hc s]

end MUB.DualGreedy


namespace MUB.DualGreedy
open Lean.Grind Std
variable {R : Type} [Field R] [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R]
  [OrderedRing R]

abbrev scaled (x : Vec4 R) (a : R) : Vec4 R := fun i => x i / a

omit [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R] in
theorem dot4_scaled (x y : Vec4 R) (a b : R) :
    dot4 (scaled x a) (scaled y b) = (dot4 x y) / (a*b) := by
  simp only [dot4, sum4, scaled, Field.div_eq_mul_inv, Field.inv_mul]
  grind

omit [IsLinearOrder R] [OrderedRing R] in
private theorem div_eq_one {a b : R} (hb : 0 < b) (h : a = b) :
    a / b = 1 := by
  rw [h, Field.div_eq_mul_inv, Field.mul_inv_cancel (Preorder.ne_of_gt hb)]

private theorem div_lt_one {a b : R} (hb : 0 < b) (h : a < b) :
    a / b < 1 := by
  rw [Field.div_eq_mul_inv, Field.IsOrdered.mul_inv_lt_iff_lt_mul _ _ hb, Semiring.one_mul]
  exact h

private theorem div_le_one {a b : R} (hb : 0 < b) (h : a ≤ b) :
    a / b ≤ 1 := by
  have hh := OrderedRing.mul_le_mul_of_nonneg_right h (Field.IsOrdered.inv_nonneg_iff.mpr (Std.le_of_lt hb))
  simpa only [Field.div_eq_mul_inv, Field.mul_inv_cancel (Preorder.ne_of_gt hb)] using hh

private theorem one_le_div {a b : R} (hb : 0 < b) (h : 1 ≤ a / b) :
    b ≤ a := by
  rw [Field.div_eq_mul_inv, Field.IsOrdered.le_mul_inv_iff_mul_le _ _ hb, Semiring.one_mul] at h
  exact h

/-- Certificate in homogeneous coordinates, precisely the tests expressible by
integer dot and determinant arithmetic. The conclusion is an unnormalized cap
inequality at any positive radius, not an intermediate cone-only claim. -/
theorem cap_of_homogeneous_cert
    {I V : Type} (head : I) (tail : List I)
    (v : V → Vec4 R) (h : V → R) (faces : I → Fin 4 → V)
    (num : I → Vec4 R) (den : I → R) (x : Vec4 R) (radius : R)
    (hr : 0 < radius) (hx : dot4 x x = radius*radius)
    (hh : ∀ i ∈ head :: tail, ∀ k, 0 < h (faces i k))
    (hd : ∀ i ∈ head :: tail, 0 < den i)
    (hDet : ∀ i ∈ head :: tail, det4 (v (faces i 0)) (v (faces i 1))
      (v (faces i 2)) (v (faces i 3)) ≠ 0)
    (hNorm : ∀ i ∈ head :: tail, dot4 (num i) (num i) ≤ den i * den i)
    (hExactly : ∀ i ∈ head :: tail, ∀ k,
      dot4 (v (faces i k)) (num i) = h (faces i k) * den i)
    (hAdjacent : ∀ i ∈ head :: tail, ∀ k, ∃ j ∈ head :: tail,
      dot4 (v (faces i k)) (num j) < h (faces i k) * den j ∧
      ∀ l, l ≠ k → dot4 (v (faces i l)) (num j) = h (faces i l) * den j) :
    ∃ i ∈ head :: tail, ∃ k : Fin 4, h (faces i k) * radius ≤ dot4 (v (faces i k)) x := by
  classical
  let q (i : V) := scaled (v i) (h i)
  let y (i : I) := scaled (num i) (den i)
  let u := scaled x radius
  have hunit : dot4 u u = 1 := by
    dsimp only [u]
    rw [dot4_scaled]
    exact div_eq_one (OrderedRing.mul_pos hr hr) hx
  have hc (i : I) (hi : i ∈ head :: tail) : ∃ c : Fin 4 → R, ∀ s,
      sum4 (fun j => c j * q (faces i j) s) = u s :=
    reconstruct_div_height_of_det_ne_zero (fun j => v (faces i j))
      (fun j => h (faces i j)) u (fun j => Preorder.ne_of_gt (hh i hi j)) (hDet i hi)
  let coeff (i : I) : Fin 4 → R := if hi : i ∈ head :: tail then (hc i hi).choose else fun _ => 0
  obtain ⟨i,hi,k,hcap⟩ := vec4_cap_of_directed_ridges head tail q faces y u coeff hunit
    (by
      intro i hi
      funext s
      unfold reconstruct coeff
      rw [dite_eq_left hi]
      exact (hc i hi).choose_spec s)
    (by
      intro i hi
      dsimp only [y]
      rw [dot4_scaled]
      exact div_le_one (OrderedRing.mul_pos (hd i hi) (hd i hi)) (hNorm i hi))
    (by
      intro i hi k
      dsimp only [q, y]
      rw [dot4_scaled]
      exact div_eq_one (OrderedRing.mul_pos (hh i hi k) (hd i hi)) (hExactly i hi k))
    (by
      intro i hi k
      obtain ⟨j,hj,hlt,heq⟩ := hAdjacent i hi k
      refine ⟨j,hj,?_,?_⟩
      · dsimp only [q,y]
        rw [dot4_scaled]
        exact div_lt_one (OrderedRing.mul_pos (hh i hi k) (hd j hj)) hlt
      · intro l hn
        dsimp only [q,y]
        rw [dot4_scaled]
        exact div_eq_one (OrderedRing.mul_pos (hh i hi l) (hd j hj)) (heq l hn))
  refine ⟨i,hi,k,?_⟩
  dsimp only [q,u] at hcap
  rw [dot4_scaled] at hcap
  exact one_le_div (OrderedRing.mul_pos (hh i hi k) hr) hcap

end MUB.DualGreedy


namespace S3Cover
open Lean.Grind Std MUB.DualGreedy

variable {R : Type} [CommRing R] [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R]
attribute [local instance] Ring.intCast

def cast4 (v : V4) : Vec4 R := fun i =>
  match i.val with
  | 0 => (v.1 : R)
  | 1 => (v.2.1 : R)
  | 2 => (v.2.2.1 : R)
  | _ => (v.2.2.2 : R)

omit [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R] in
theorem dot4_cast (a b : V4) : dot4 (cast4 a : Vec4 R) (cast4 b) = (dot a b : R) := by
  unfold dot4 sum4 dot
  simp only [cast4, Ring.intCast_add, Ring.intCast_mul]
  grind

def rawNormal (caps : List Cap) (i : Nat) : Vec4 R := cast4 (capAt caps i).v
def height (caps : List Cap) (i : Nat) : R := ((capAt caps i).h : R)
def rawDual (f : Facet) : Vec4 R := cast4 f.num
def denom (f : Facet) : R := (f.den : R)

theorem cast_int_lt {a b : Int} (h : a < b) : (a : R) < (b : R) := by
  have hp := OrderedRing.pos_intCast_of_pos (R := R) (b - a) (by omega)
  rw [Ring.intCast_sub] at hp
  exact OrderedAdd.sub_pos_iff.mp hp

theorem cast_int_le {a b : Int} (h : a ≤ b) : (a : R) ≤ (b : R) := by
  have hp := OrderedRing.nonneg_intCast_of_nonneg (R := R) (b - a) (by omega)
  rw [Ring.intCast_sub] at hp
  exact OrderedAdd.sub_nonneg_iff.mp hp

theorem raw_height_pos {caps : List Cap} {fs : List Facet}
    (h : certificate caps fs = true) (f : Facet) (hf : f ∈ fs) (k : Fin 4) :
    0 < (height caps (index4 f.idx k) : R) := by
  exact OrderedRing.pos_intCast_of_pos (R := R) _
    (certificate_caps h _ (List.fst_mem_of_mem_zipIdx
      (index4_get (certificate_face h f hf).1 k))).1

theorem raw_dual_bound {caps : List Cap} {fs : List Facet}
    (h : certificate caps fs = true) (f : Facet) (hf : f ∈ fs) :
    0 < (denom f : R) ∧ dot4 (rawDual f : Vec4 R) (rawDual f) ≤ denom f * denom f := by
  have hv := facet_values (certificate_face h f hf).1
  refine ⟨OrderedRing.pos_intCast_of_pos _ hv.1, ?_⟩
  simpa only [rawDual, denom, dot4_cast, Ring.intCast_mul] using cast_int_le (R := R) hv.2.1

omit [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R] in
theorem raw_support_own {caps : List Cap} {fs : List Facet}
    (h : certificate caps fs = true) (f : Facet) (hf : f ∈ fs) (k : Fin 4) :
    dot4 (rawNormal caps (index4 f.idx k) : Vec4 R) (rawDual f) =
      height caps (index4 f.idx k) * denom f := by
  have hv := (certificate_face h f hf).1
  have hs := facet_support hv (index4 f.idx k) _ (index4_get hv k)
  rw [ite_eq_left (index4_mem _ k)] at hs
  simpa only [rawNormal, rawDual, height, denom, dot4_cast, Ring.intCast_mul]
    using congrArg (fun n : Int => (n : R)) hs

theorem raw_support_directed {caps : List Cap} {fs : List Facet}
    (h : certificate caps fs = true) (f : Facet) (hf : f ∈ fs) (k : Fin 4) :
    ∃ g ∈ fs,
      dot4 (rawNormal caps (index4 f.idx k) : Vec4 R) (rawDual g) <
        height caps (index4 f.idx k) * denom g ∧
      ∀ l, l ≠ k →
        dot4 (rawNormal caps (index4 f.idx l) : Vec4 R) (rawDual g) =
          height caps (index4 f.idx l) * denom g := by
  have hv := (certificate_face h f hf).1
  obtain ⟨g, hg, hk, hrest⟩ := certificate_directed_strict h f hf
    (index4 f.idx k) _ (index4_mem _ k) (index4_get hv k)
  refine ⟨g, hg, ?_, ?_⟩
  · simpa only [rawNormal, rawDual, height, denom, dot4_cast, Ring.intCast_mul]
      using cast_int_lt (R := R) hk
  · intro l hn
    have hneq : index4 f.idx l ≠ index4 f.idx k := fun he =>
      hn (index4_inj (validFacet_ordered hv) he)
    have he := hrest _ _ (index4_mem _ l) hneq (index4_get hv l)
    simpa only [rawNormal, rawDual, height, denom, dot4_cast, Ring.intCast_mul]
      using congrArg (fun n : Int => (n : R)) he

end S3Cover


namespace S3Cover
open Lean.Grind Std MUB.DualGreedy

variable {R : Type} [Field R] [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R]
attribute [local instance] Ring.intCast

omit [LE R] [LT R] [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R] in
theorem det4_cast (a b c d : V4) :
    MUB.DualGreedy.det4 (cast4 a : Vec4 R) (cast4 b) (cast4 c) (cast4 d) =
      (S3Cover.det4 a b c d : R) := by
  simp [MUB.DualGreedy.det4, MUB.DualGreedy.det3, S3Cover.det4, S3Cover.det3,
    cast4, Ring.intCast_add, Ring.intCast_sub, Ring.intCast_mul]

theorem raw_det_ne_zero {caps : List Cap} {fs : List Facet}
    (h : certificate caps fs = true) (f : Facet) (hf : f ∈ fs) :
    MUB.DualGreedy.det4
      (rawNormal caps (index4 f.idx 0) : Vec4 R)
      (rawNormal caps (index4 f.idx 1))
      (rawNormal caps (index4 f.idx 2))
      (rawNormal caps (index4 f.idx 3)) ≠ 0 := by
  obtain ⟨_,_,a,b,c,d,ha,hb,hc,hd,he⟩ := facet_values (certificate_face h f hf).1
  change MUB.DualGreedy.det4
    (rawNormal caps f.idx.1 : Vec4 R) (rawNormal caps f.idx.2.1)
    (rawNormal caps f.idx.2.2.1) (rawNormal caps f.idx.2.2.2) ≠ 0
  simp only [rawNormal, capAt, ha, hb, hc, hd, Option.getD_some, det4_cast]
  intro hzero
  have hle : (0 : Int) ≤ S3Cover.det4 a.v b.v c.v d.v :=
    OrderedRing.le_of_intCast_le_intCast (R := R) 0 _ (by simp [Ring.intCast_zero, hzero])
  have hge : S3Cover.det4 a.v b.v c.v d.v ≤ (0 : Int) :=
    OrderedRing.le_of_intCast_le_intCast (R := R) _ 0 (by simp [Ring.intCast_zero, hzero])
  exact he (by omega)

/-- End-to-end: the executable certificate implies exact coverage of the
sphere of every positive radius over every linearly ordered field. -/
theorem sphereCovered {caps : List Cap} {fs : List Facet}
    (h : certificate caps fs = true) (w : Vec4 R) (r : R)
    (hr : 0 < r) (hw : dot4 w w = r*r) :
    ∃ c ∈ caps, (c.h : R) * r ≤ dot4 (cast4 c.v : Vec4 R) w := by
  cases fs with
  | nil => exact False.elim (certificate_nonempty h rfl)
  | cons f fs =>
    obtain ⟨g,hg,k,hk⟩ := cap_of_homogeneous_cert f fs
      (rawNormal caps) (height caps) (fun g => index4 g.idx) rawDual denom w r hr hw
      (fun g hg k => raw_height_pos h g hg k)
      (fun g hg => (raw_dual_bound h g hg).1)
      (fun g hg => raw_det_ne_zero h g hg)
      (fun g hg => (raw_dual_bound h g hg).2)
      (fun g hg k => raw_support_own h g hg k)
      (fun g hg k => raw_support_directed h g hg k)
    exact ⟨capAt caps (index4 g.idx k),
      List.fst_mem_of_mem_zipIdx (index4_get (certificate_face h g hg).1 k), hk⟩

end S3Cover

/- First concrete consumer: seed 2762 from the pinned NoFourMUBS atlas. -/

namespace S3Cover

def caps2762 : List Cap := [
  ⟨(222129108180818460672, -112631379325588865024, 156947954970757431296, 21271038426378928128), 8854437156573355⟩,
  ⟨(-6622273876262912, -14666911333744640, -6325135338373120, 5053554905579520), 1220997118212435⟩,
  ⟨(-32481980444573696, 4356795095056384, 13479066019561472, -6506018540355584), 1004384221135735⟩,
  ⟨(-2404147403948032, 26738512577429504, 13724731203125248, 65446165927165952), 4901580642816267⟩,
  ⟨(-5884607639584768, 9651424954679296, -44238473728622592, -55744736882851840), 5839463122471863⟩
]
def faces2762 : List Facet := [
  ⟨(0, 1, 2, 3), (-6818510185602764662585416188222265074077699215, -6451850505951285517142973207221168769894967780, 3258677780052944782563038398637586036972041801, 13060424378181885761879545786056927307327401783), 151656995849373318450715611008852196838575439872⟩,
  ⟨(0, 1, 2, 4), (-7132559356693033687534341016167825637775850245, -24219598281390951774264592612645126081965918735, -3772337970569450521184752880918529577723891793, -25825340769134742760778178729901209953011059679), 242270213657574970168319120880831889990202949632⟩,
  ⟨(0, 1, 3, 4), (14776784730191335594498244584137670027331583640, 780333661527651131055060696917493522352454578, -21614816795149510521578503738298568194429238409, 9330907990001398016875104936163041925299736947), 61072951081773579940383023055312724916260831232⟩,
  ⟨(0, 2, 3, 4), (5659791942212791670157081180484893435402424196, 19542431235093907487371066427999598985704171270, 6896729988519810518864615781243182972782910814, -6497995020132304224674650647009413146628018387), 36379177912982356651825692359631405167954362368⟩,
  ⟨(1, 2, 3, 4), (-6471609873634330173615880467812688137818885, 4513362035415997323725154353714529993913151, -10866244154685481966976963748865427224679141, 4320534531128688427817601156190678470449973), 55056817565727189836086445590614993279123456⟩
]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem actual_2762_certificate : certificate caps2762 faces2762 = true := by decide

open Lean.Grind Std MUB.DualGreedy

set_option maxRecDepth 100000 in
example {R : Type} [Field R] [LE R] [LT R] [IsLinearOrder R]
    [LawfulOrderLT R] [OrderedRing R] (w : Vec4 R) (r : R)
    (hr : 0 < r) (hw : dot4 w w = r * r) :
    letI : IntCast R := Ring.intCast
    ∃ c ∈ caps2762, (c.h : R) * r ≤ dot4 (cast4 c.v : Vec4 R) w := by
  exact sphereCovered actual_2762_certificate w r hr hw

end S3Cover
end D5.S3.Quantum.Tomography.MUB.BoundarySphereCover
