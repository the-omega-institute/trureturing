/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/BasedLoopCoordinateTransport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/BasedLoopCoordinateTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Closed RS loops change coefficient basis through two triangles before endpoint cancellation. -/
import D5.S3.ConceptDynamics.Coding.FiniteKernelLadder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SourceOnly.BasedLoopCoordinateTransport
open D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
open SourceOnly.KernelRSSquareGyration (rows rows_comp value)
open SourceOnly.FiniteKernelLadder (D Mat Based Path rows_id rows_one rows_injective rowUnit)

universe u
variable {V : Type u} [AddCommGroup V] [Module D V]
variable {n m : ℕ}

/-- Actual coefficient change: old coefficients multiplied on the RIGHT
by C become new coefficients. It is rectangular if the index types differ. -/
def changeRows (b : Module.Basis (Fin n) D V)
    (c : Module.Basis (Fin m) D V) : Mat n m := rows b c LinearMap.id

theorem changeRows_inverse (b : Module.Basis (Fin n) D V)
    (c : Module.Basis (Fin m) D V) :
    changeRows b c * changeRows c b = 1 := by
  unfold changeRows
  rw [← rows_comp, LinearMap.id_comp, rows_id]

/-- This is used separately for BOTH actual RS factors. -/
theorem factor_coordinates (b : Module.Basis (Fin n) D V)
    (c : Module.Basis (Fin m) D V) (f : Module.End D V) :
    rows b b f * changeRows b c = changeRows b c * rows c c f := by
  unfold changeRows
  rw [← rows_comp, ← rows_comp, LinearMap.id_comp, LinearMap.comp_id]

/-- Inverse of the existing coordinate equivalence; not an inverse of time. -/
def fromRows (b : Module.Basis (Fin n) D V) (M : Mat n n) : Module.End D V :=
  (LinearMap.toMatrix b b).symm M.transpose

theorem rows_fromRows (b : Module.Basis (Fin n) D V) (M : Mat n n) :
    rows b b (fromRows b M) = M := by
  unfold rows fromRows
  rw [LinearEquiv.apply_symm_apply, Matrix.transpose_transpose]

/-- An actual endomorphism unit recovered from the actual row unit supplied
by the finite kernel ladder. Both inverse laws use faithful coordinates. -/
def linearUnit (b : Module.Basis (Fin n) D V) (U : (Mat n n)ˣ) :
    (Module.End D V)ˣ where
  val := fromRows b (U : Mat n n)
  inv := fromRows b (↑U⁻¹ : Mat n n)
  val_inv := by
    apply rows_injective b b
    change rows b b ((fromRows b (U : Mat n n)).comp
      (fromRows b (↑U⁻¹ : Mat n n))) = rows b b (1 : Module.End D V)
    rw [rows_comp, rows_fromRows, rows_fromRows, Units.inv_mul, rows_one]
  inv_val := by
    apply rows_injective b b
    change rows b b ((fromRows b (↑U⁻¹ : Mat n n)).comp
      (fromRows b (U : Mat n n))) = rows b b (1 : Module.End D V)
    rw [rows_comp, rows_fromRows, rows_fromRows, Units.mul_inv, rows_one]

/-- The COLUMN backward factor is T a^{-1}. Endpoint commutation proves
that it is also a^{-1} T; neither order is silently interchanged. -/
theorem inverse_time_order (a : (Module.End D V)ˣ) (T : Module.End D V)
    (hc : Commute (a : Module.End D V) T) :
    T * (↑a⁻¹ : Module.End D V) = (↑a⁻¹ : Module.End D V) * T := by
  calc
    T * (↑a⁻¹ : Module.End D V) =
        (↑a⁻¹ : Module.End D V) * ((a : Module.End D V) * T) * ↑a⁻¹ := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = (↑a⁻¹ : Module.End D V) * (T * (a : Module.End D V)) * ↑a⁻¹ := by
          rw [hc.eq]
    _ = (↑a⁻¹ : Module.End D V) * T := by
          rw [mul_assoc, mul_assoc, Units.mul_inv, mul_one]

/-- Both endpoint cochains are LITERALLY the same term, because sr=rs=T.
This consumed helper admits singular T and zero ranks. The RS hypotheses
are equations of maps and are constructed, not assumed, in the path client. -/
theorem closed_square {d : ℕ} [NeZero d] (hd : 3 ∣ d)
    (b : Module.Basis (Fin n) D V) (c : Module.Basis (Fin m) D V)
    (r s T : Module.End D V) (hsr : s.comp r = T) (hrs : r.comp s = T) :
    value (d := d) b b r s + value (d := d) b c LinearMap.id T =
      value (d := d) b c LinearMap.id T + value (d := d) c c r s := by
  have h₁ := SourceOnly.KernelRSSquareGyration.value_triangle (d := d) hd b b c r LinearMap.id s
  have h₂ := SourceOnly.KernelRSSquareGyration.value_triangle (d := d) hd b c c LinearMap.id r s
  simp only [LinearMap.comp_id, LinearMap.id_comp, hsr, hrs] at h₁ h₂
  exact h₁.trans h₂.symm

/-- A genuine downstream consumer of the finite-ladder one-edge theorem.
The loop unit is recovered as an actual map. The new basis is arbitrary,
but equality is DERIVED from RS triangles, not supplied as a premise.
All rectangular/singular intermediates remain inside the original path.
-/
theorem path_rebased {X : Based.{u}} {k : ℕ} (w : Path X X k)
    (ht : IsUnit X.time) (c : Module.Basis (Fin m) D X.V) :
    ∃ a : (Module.End D X.V)ˣ,
      (a : Module.End D X.V) = w.forward ∧
      Commute (a : Module.End D X.V) X.time ∧
      let s : Module.End D X.V := X.time * (↑a⁻¹ : Module.End D X.V)
      rows X.basis X.basis (a : Module.End D X.V) * changeRows X.basis c =
        changeRows X.basis c * rows c c (a : Module.End D X.V) ∧
      rows X.basis X.basis s * changeRows X.basis c =
        changeRows X.basis c * rows c c s ∧
      s.comp (a : Module.End D X.V) = X.time ∧
      (a : Module.End D X.V).comp s = X.time ∧
      ∀ (d : ℕ) [NeZero d], 3 ∣ d →
        (w.weight d + value (d := d) X.basis c LinearMap.id X.time =
          value (d := d) X.basis c LinearMap.id X.time +
            dyadicGyration d (rowUnit c a : Mat m m)
              ((↑(rowUnit c a)⁻¹ : Mat m m) * rows c c X.time)) ∧
        w.weight d = dyadicGyration d (rowUnit c a : Mat m m)
          ((↑(rowUnit c a)⁻¹ : Mat m m) * rows c c X.time) := by
  obtain ⟨v,U,hv,hU,hcomm,hweight⟩ :=
    SourceOnly.FiniteKernelLadder.arbitrary_loop_one_edge w ht
  let a := linearUnit X.basis U
  have ha : (a : Module.End D X.V) = w.forward := by
    apply rows_injective X.basis X.basis
    exact (rows_fromRows X.basis (U : Mat X.dim X.dim)).trans hU
  have hc : Commute (a : Module.End D X.V) X.time := by
    change (a : Module.End D X.V) * X.time = X.time * (a : Module.End D X.V)
    apply rows_injective X.basis X.basis
    change rows X.basis X.basis ((a : Module.End D X.V).comp X.time) =
      rows X.basis X.basis (X.time.comp (a : Module.End D X.V))
    rw [rows_comp, rows_comp, show rows X.basis X.basis
      (a : Module.End D X.V) = (U : Mat X.dim X.dim) from
        rows_fromRows X.basis (U : Mat X.dim X.dim)]
    exact hcomm.eq.symm
  let s : Module.End D X.V := X.time * (↑a⁻¹ : Module.End D X.V)
  have hsr : s.comp (a : Module.End D X.V) = X.time := by
    change (X.time * (↑a⁻¹ : Module.End D X.V)) * (a : Module.End D X.V) = X.time
    rw [mul_assoc, Units.inv_mul, mul_one]
  have hrs : (a : Module.End D X.V).comp s = X.time := by
    change (a : Module.End D X.V) * (X.time * (↑a⁻¹ : Module.End D X.V)) = X.time
    rw [← mul_assoc, hc.eq, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨a,ha,hc, factor_coordinates X.basis c _,
    factor_coordinates X.basis c s,hsr,hrs,?_⟩
  intro d _ hd
  have hw : w.weight d = value (d := d) X.basis X.basis
      (a : Module.End D X.V) s := by
    calc
      w.weight d = dyadicGyration d (U : Mat X.dim X.dim)
          ((↑U⁻¹ : Mat X.dim X.dim) * X.matrix) := by
            simpa only [← hU] using (hweight d hd).2
      _ = _ := by
        change _ = dyadicGyration d (rows X.basis X.basis (fromRows X.basis ↑U))
          (rows X.basis X.basis (X.time.comp (fromRows X.basis ↑U⁻¹)))
        rw [rows_comp, rows_fromRows, rows_fromRows]
        rfl
  have hnew : value (d := d) c c (a : Module.End D X.V) s =
      dyadicGyration d (rowUnit c a : Mat m m)
        ((↑(rowUnit c a)⁻¹ : Mat m m) * rows c c X.time) := by
    change dyadicGyration d (rows c c (a : Module.End D X.V))
      (rows c c (X.time.comp (↑a⁻¹ : Module.End D X.V))) = _
    rw [rows_comp]
    rfl
  have hsq := closed_square hd X.basis c (a : Module.End D X.V) s X.time hsr hrs
  rw [← hw, hnew] at hsq
  refine ⟨hsq,?_⟩
  exact add_left_cancel ((add_comm _ _).trans hsq)

end SourceOnly.BasedLoopCoordinateTransport
