/- GID: D5/S3/FiniteGroups/Heisenberg/DeterminantCharts
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Heisenberg/DeterminantCharts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized charts for determinant-zero incidence over length-two residue coordinates. -/

import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-! # Determinant incidence in normalized residue charts -/

namespace D5.S3.FiniteGroups.Heisenberg

/-- Coordinates needed for the two specific length-two coefficient rings. -/
structure ResidueCoordinates (R K : Type*) [CommRing R] [Field K] where
  code : R ≃ K × K
  res : R →+* K
  res_code (x : R) : res x = (code x).1
  code_zero : code 0 = (0, 0)
  unit_iff (x : R) : IsUnit x ↔ res x ≠ 0
  nil_mul (a : K) (x : R) :
    code.symm (0, a) * x = code.symm (0, a * res x)

namespace ResidueCoordinates

variable {R K : Type*} [CommRing R] [Field K] (C : ResidueCoordinates R K)

def nil (a : K) : R := C.code.symm (0, a)

private theorem res_nil (a : K) : C.res (C.nil a) = 0 := by
  rw [C.res_code]; simp [nil]

private theorem nil_inj {a b : K} : C.nil a = C.nil b ↔ a = b := by
  simp [nil, C.code.symm.injective.eq_iff]

private theorem nil_zero : C.nil 0 = 0 := by
  apply C.code.injective
  simp [nil, C.code_zero]

private theorem eq_nil {x : R} (hx : C.res x = 0) : x = C.nil (C.code x).2 := by
  apply C.code.injective
  simpa [nil, Prod.ext_iff, ← C.res_code] using hx

private theorem res_unit (u : Rˣ) : C.res (u : R) ≠ 0 :=
  (C.unit_iff _).mp u.isUnit

private theorem nil_nil (a b : K) : C.nil a * C.nil b = 0 := by
  rw [show C.nil a * C.nil b = C.nil (a * C.res (C.nil b)) from C.nil_mul a _,
    C.res_nil, mul_zero, C.nil_zero]

abbrev Chart (R K : Type*) [CommRing R] :=
  (Rˣ × R) ⊕ ((K × Rˣ) ⊕ (K × K))

def decode : Chart R K → R × R
  | .inl (u, t) => (u, (u : R) * t)
  | .inr (.inl (s, u)) => ((u : R) * C.nil s, u)
  | .inr (.inr (a, b)) => (C.nil a, C.nil b)

private theorem decode_injective : Function.Injective C.decode := by
  intro a b0 h
  rcases a with ⟨u, t⟩ | (⟨s, u⟩ | ⟨a, b⟩) <;>
    rcases b0 with ⟨v, w⟩ | (⟨r, v⟩ | ⟨c, d⟩)
  · have hu : u = v := Units.ext (congrArg Prod.fst h)
    subst v
    have ht : t = w := (u.mul_right_inj).mp (congrArg Prod.snd h)
    subst w; rfl
  · have hh := congrArg (fun z : R × R => C.res z.1) h
    have hz : C.res (u : R) = 0 := by simpa [decode, map_mul, C.res_nil] using hh
    exact (C.res_unit u hz).elim
  · have hh := congrArg (fun z : R × R => C.res z.1) h
    have hz : C.res (u : R) = 0 := by simpa [decode, C.res_nil] using hh
    exact (C.res_unit u hz).elim
  · have hh := congrArg (fun z : R × R => C.res z.1) h
    have hz : C.res (v : R) = 0 := by simpa [decode, map_mul, C.res_nil] using hh.symm
    exact (C.res_unit v hz).elim
  · have hu : u = v := Units.ext (congrArg Prod.snd h)
    subst v
    have hs : s = r := C.nil_inj.mp ((u.mul_right_inj).mp (congrArg Prod.fst h))
    subst r; rfl
  · have hh := congrArg (fun z : R × R => C.res z.2) h
    have hz : C.res (u : R) = 0 := by simpa [decode, C.res_nil] using hh
    exact (C.res_unit u hz).elim
  · have hh := congrArg (fun z : R × R => C.res z.1) h
    have hz : C.res (v : R) = 0 := by simpa [decode, C.res_nil] using hh.symm
    exact (C.res_unit v hz).elim
  · have hh := congrArg (fun z : R × R => C.res z.2) h
    have hz : C.res (v : R) = 0 := by simpa [decode, C.res_nil] using hh.symm
    exact (C.res_unit v hz).elim
  · have ha := C.nil_inj.mp (congrArg Prod.fst h)
    have hb := C.nil_inj.mp (congrArg Prod.snd h)
    subst c; subst d; rfl

private theorem decode_surjective : Function.Surjective C.decode := by
  classical
  rintro ⟨x, y⟩
  by_cases hx : IsUnit x
  · refine ⟨.inl (hx.unit, (↑hx.unit⁻¹ : R) * y), ?_⟩
    simp [decode, ← mul_assoc, hx.unit_spec]
  · have hx0 : C.res x = 0 := by simpa [C.unit_iff] using hx
    by_cases hy : IsUnit y
    · let u := hy.unit
      have hu : (u : R) = y := hy.unit_spec
      have hnil : (↑u⁻¹ : R) * x = C.nil (C.code ((↑u⁻¹ : R) * x)).2 :=
        C.eq_nil (by simp [map_mul, hx0])
      refine ⟨.inr (.inl ((C.code ((↑u⁻¹ : R) * x)).2, u)), ?_⟩
      apply Prod.ext
      · change (u : R) * C.nil _ = x
        rw [← hnil]; simp [← mul_assoc]
      · exact hu
    · have hy0 : C.res y = 0 := by simpa [C.unit_iff] using hy
      exact ⟨.inr (.inr ((C.code x).2, (C.code y).2)),
        Prod.ext (C.eq_nil hx0).symm (C.eq_nil hy0).symm⟩

noncomputable def chartEquiv : Chart R K ≃ R × R :=
  Equiv.ofBijective C.decode ⟨C.decode_injective, C.decode_surjective⟩

/-- Incidence expressed in the three disjoint charts. -/
def chartRel : Chart R K → Chart R K → Prop
  | .inl (_, t), .inl (_, w) => t = w
  | .inl _, .inr (.inl _) => False
  | .inr (.inl _), .inl _ => False
  | .inr (.inl (s, _)), .inr (.inl (r, _)) => s = r
  | .inl (_, t), .inr (.inr (a, b)) => b = C.res t * a
  | .inr (.inr (a, b)), .inl (_, t) => b = C.res t * a
  | .inr (.inl _), .inr (.inr (a, _)) => a = 0
  | .inr (.inr (a, _)), .inr (.inl _) => a = 0
  | .inr (.inr _), .inr (.inr _) => True

private theorem decode_rel (a b0 : Chart R K) :
    (C.decode a).1 * (C.decode b0).2 = (C.decode b0).1 * (C.decode a).2 ↔
      C.chartRel a b0 := by
  rcases a with ⟨u, t⟩ | (⟨s, u⟩ | ⟨a, b⟩) <;>
    rcases b0 with ⟨v, w⟩ | (⟨r, v⟩ | ⟨c, d⟩)
  · change (u : R) * ((v : R) * w) = (v : R) * ((u : R) * t) ↔ t = w
    rw [show (u : R) * ((v : R) * w) = ((u * v : Rˣ) : R) * w by simp [mul_assoc],
      show (v : R) * ((u : R) * t) = ((u * v : Rˣ) : R) * t by simp [mul_left_comm, mul_assoc],
      (u * v).mul_right_inj]
    exact eq_comm
  · change _ ↔ False
    refine iff_false_intro fun h => ?_
    have hh := congrArg C.res h
    simpa [decode, map_mul, C.res_nil, mul_eq_zero, C.res_unit] using hh
  · change (u : R) * C.nil d = C.nil c * ((u : R) * t) ↔ d = C.res t * c
    rw [show C.nil c * ((u : R) * t) = (u : R) * (C.nil c * t) by ring,
      u.mul_right_inj, show C.nil c * t = C.nil (c * C.res t) from C.nil_mul c t,
      C.nil_inj, mul_comm c]
  · change _ ↔ False
    refine iff_false_intro fun h => ?_
    have hh := congrArg C.res h
    simpa [decode, map_mul, C.res_nil, mul_eq_zero, C.res_unit] using hh
  · change ((u : R) * C.nil s) * (v : R) = ((v : R) * C.nil r) * (u : R) ↔ s = r
    rw [show ((u : R) * C.nil s) * (v : R) = ((u * v : Rˣ) : R) * C.nil s by simp [mul_right_comm, mul_assoc],
      show ((v : R) * C.nil r) * (u : R) = ((u * v : Rˣ) : R) * C.nil r by simp [mul_left_comm, mul_right_comm, mul_assoc],
      (u * v).mul_right_inj, C.nil_inj]
  · change ((u : R) * C.nil s) * C.nil d = C.nil c * (u : R) ↔ c = 0
    rw [mul_assoc, C.nil_nil, mul_zero, mul_comm (C.nil c),
      ← mul_zero (u : R), u.mul_right_inj, eq_comm, ← C.nil_zero, C.nil_inj]
  · change C.nil a * ((v : R) * w) = (v : R) * C.nil b ↔ b = C.res w * a
    rw [eq_comm]
    rw [show C.nil a * ((v : R) * w) = (v : R) * (C.nil a * w) by ring,
      v.mul_right_inj, show C.nil a * w = C.nil (a * C.res w) from C.nil_mul a w,
      C.nil_inj, mul_comm a]
  · change C.nil a * (v : R) = ((v : R) * C.nil r) * C.nil b ↔ a = 0
    rw [mul_assoc, C.nil_nil, mul_zero, mul_comm (C.nil a),
      ← mul_zero (v : R), v.mul_right_inj, ← C.nil_zero, C.nil_inj]
  · change C.nil a * C.nil d = C.nil c * C.nil b ↔ True
    simp [C.nil_nil]

abbrev UnitCode (K : Type*) [Zero K] := {a : K × K // a.1 ≠ 0}

noncomputable def unitCode : Rˣ ≃ UnitCode K where
  toFun u := ⟨C.code u, by rw [← C.res_code]; exact C.res_unit u⟩
  invFun a := ((C.unit_iff _).mpr (by rw [C.res_code, C.code.apply_symm_apply]; exact a.property)).unit
  left_inv u := by
    apply Units.ext
    exact (IsUnit.unit_spec _).trans (C.code.symm_apply_apply (u : R))
  right_inv a := by
    apply Subtype.ext
    change C.code ((IsUnit.unit _ : Rˣ) : R) = a.val
    rw [IsUnit.unit_spec, C.code.apply_symm_apply]

abbrev NormalChart (K : Type*) [Zero K] :=
  (UnitCode K × (K × K)) ⊕ ((K × UnitCode K) ⊕ (K × K))

noncomputable def codeChart : Chart R K ≃ NormalChart K :=
  Equiv.sumCongr (Equiv.prodCongr C.unitCode C.code)
    (Equiv.sumCongr (Equiv.prodCongr (Equiv.refl K) C.unitCode) (Equiv.refl _))

/-- A common relation, retaining both the fine slope and its residue direction. -/
def normalRel : NormalChart K → NormalChart K → Prop
  | .inl (_, t), .inl (_, w) => t = w
  | .inl _, .inr (.inl _) => False
  | .inr (.inl _), .inl _ => False
  | .inr (.inl (s, _)), .inr (.inl (r, _)) => s = r
  | .inl (_, t), .inr (.inr (a, b)) => b = t.1 * a
  | .inr (.inr (a, b)), .inl (_, t) => b = t.1 * a
  | .inr (.inl _), .inr (.inr (a, _)) => a = 0
  | .inr (.inr (a, _)), .inr (.inl _) => a = 0
  | .inr (.inr _), .inr (.inr _) => True

private theorem codeChart_rel (a b : Chart R K) :
    normalRel (C.codeChart a) (C.codeChart b) ↔ C.chartRel a b := by
  rcases a with ⟨u, t⟩ | (⟨s, u⟩ | ⟨c, d⟩) <;>
    rcases b with ⟨v, w⟩ | (⟨r, v⟩ | ⟨e, f⟩) <;>
    simp [codeChart, normalRel, chartRel, C.code.injective.eq_iff, ← C.res_code]

noncomputable def normalForm : (R × R) ≃ NormalChart K :=
  C.chartEquiv.symm.trans C.codeChart

private theorem normalForm_rel (v w : R × R) :
    v.1 * w.2 = w.1 * v.2 ↔ normalRel (C.normalForm v) (C.normalForm w) := by
  have h := C.decode_rel (C.chartEquiv.symm v) (C.chartEquiv.symm w)
  change (C.chartEquiv (C.chartEquiv.symm v)).1 *
      (C.chartEquiv (C.chartEquiv.symm w)).2 =
      (C.chartEquiv (C.chartEquiv.symm w)).1 *
      (C.chartEquiv (C.chartEquiv.symm v)).2 ↔ _ at h
  rw [C.chartEquiv.apply_symm_apply, C.chartEquiv.apply_symm_apply] at h
  exact h.trans (C.codeChart_rel _ _).symm

variable {S : Type*} [CommRing S]

noncomputable def determinantEquiv (D : ResidueCoordinates S K) : (R × R) ≃ (S × S) :=
  C.normalForm.trans D.normalForm.symm

/-- Equality of cross products is preserved for every pair, including nilpotent vectors. -/
theorem determinantEquiv_preserves (D : ResidueCoordinates S K) (v w : R × R) :
    v.1 * w.2 = w.1 * v.2 ↔
      (C.determinantEquiv D v).1 * (C.determinantEquiv D w).2 =
      (C.determinantEquiv D w).1 * (C.determinantEquiv D v).2 := by
  rw [C.normalForm_rel, D.normalForm_rel]
  simp [determinantEquiv]

end ResidueCoordinates
end D5.S3.FiniteGroups.Heisenberg
