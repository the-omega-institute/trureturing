/- GID: D5/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/GeneralizedCHSHGroupDecomposition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Uniform cyclic-by-abelian decomposition of the generalized CHSH groups. -/

/-
Declaration inventory (generated from this source; consumers are declarations whose proof/value uses the name):
P0 (abbrev): proof_shape: not-applicable; escape_witness: none; consumers: rels, fg_relations, x_order, y_order, z_order, zx, zy, delta_square_half.
P1 (abbrev): proof_shape: not-applicable; escape_witness: none; consumers: rels, fg_relations, x_order, y_order, z_order, zx, zy, delta_square_half.
J (abbrev): proof_shape: not-applicable; escape_witness: none; consumers: rels, fg_relations, x_order, y_order, z_order, zx, zy, delta_square_half.
rels (def): proof_shape: not-applicable; escape_witness: none; consumers: G, fg_relations, forward, forward_of, delta, x_order, y_order, z_order, zx, zy, delta_square_half, delta_square_neg, delta_square_nat, delta_square, delta_swap, delta_commute, ks_coe, ks_square_z, backL_s, backL_e, backR_cg, back_generator, back_compat, backward, backL_square, backward_forward, ks_succ_coe, forward_ks, forward_backward.
G (abbrev): proof_shape: not-applicable; escape_witness: none; consumers: claim, forward, forward_of, delta, x_order, y_order, z_order, zx, zy, delta_square_half, delta_square_neg, delta_square_nat, delta_square, delta_swap, delta_commute, kgens, K_isMulCommutative, kd, ks, ks_coe, ks_square_z, ks_square, ks_order, ks_prod, kt, kt_square, kernelHom, kernelHom_s, kernelHom_t, kt_last, kernelHom_u, kernelHom_e, backL, backL_s, backL_e, backL_t, backR_cg, back_generator, back_compat, backward, backL_square, backward_forward, ks_succ_coe, forward_ks, forward_backward, result.
L (abbrev): proof_shape: not-applicable; escape_witness: none; consumers: s, t, s_order, t_square, liftL, liftL_s, liftL_t, L_hom_ext, ts, ts_square, u, e, u_zero, u_end, u_last, u_basis, u_square, e_square, e_order, step, step_s, step_t, e_zero, e_end, step_e_basis, ts_eq_range, prod_e, step_e_last, step_e, step_iter_s, step_period, stepAut, stepAut_period, alpha, claim, alpha_generator, v, pref, r_order, c_order, step_s_square, c_commute_r, c_commute_v, pref_end, pref_square, v_pow, v_order, rv_relation, fg, fg_relations, forward, forward_of, kernelHom, kernelHom_s, kernelHom_t, kernelHom_u, kernelHom_e, backL, backL_s, backL_e, backL_t, back_generator, back_compat, backward, backL_square, backward_forward, forward_ks, forward_backward, result.
cyclicHom (def): proof_shape: not-applicable; escape_witness: none; consumers: cyclicHom_int, cyclicHom_one, liftL, liftL_s, liftL_t, alpha, alpha_generator, backR_cg, back_compat, backward, forward_backward.
cyclicHom_int (theorem): proof_shape: bind-only; escape_witness: none; consumers: cyclicHom_one, liftL.
cyclicHom_one (theorem): proof_shape: bind-only; escape_witness: none; consumers: liftL_s, liftL_t, alpha_generator, backR_cg.
cyclicHom_ext (theorem): proof_shape: bind-only; escape_witness: none; consumers: L_hom_ext, forward_backward.
s (def): proof_shape: not-applicable; escape_witness: none; consumers: s_order, liftL_s, L_hom_ext, u, e, u_zero, u_end, u_last, u_basis, u_square, e_square, e_order, step, step_s, e_zero, e_end, step_e_basis, prod_e, step_e_last, step_e, step_iter_s, step_period, v, c_order, step_s_square, c_commute_r, c_commute_v, pref_end, pref_square, v_pow, rv_relation, fg, fg_relations, kernelHom_s, kernelHom_u, kernelHom_e, backL_s, back_generator, backL_square, backward_forward, forward_ks, forward_backward.
t (def): proof_shape: not-applicable; escape_witness: none; consumers: t_square, liftL_t, L_hom_ext, ts, ts_square, u, u_zero, u_end, u_last, u_basis, u_square, step_t, step_e_basis, ts_eq_range, step_e_last, step_period, kernelHom_t, kernelHom_u, backL_t, back_generator, forward_backward.
s_order (theorem): proof_shape: bind-only; escape_witness: none; consumers: u_square, e_order, prod_e, c_order.
t_square (theorem): proof_shape: bind-only; escape_witness: none; consumers: ts_square, u_square.
liftL (def): proof_shape: not-applicable; escape_witness: none; consumers: liftL_s, liftL_t, step, kernelHom.
liftL_s (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_s, kernelHom_s.
liftL_t (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_t, kernelHom_t.
L_hom_ext (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_period, back_generator, forward_backward.
ts (def): proof_shape: not-applicable; escape_witness: none; consumers: ts_square, u, u_zero, u_end, u_last, u_basis, u_square, ts_eq_range, prod_e, step_e_last, kernelHom_u.
ts_square (theorem): proof_shape: bind-only; escape_witness: none; consumers: u_square, prod_e.
u (def): proof_shape: not-applicable; escape_witness: none; consumers: e, u_zero, u_end, u_last, u_basis, u_square, e_square, e_zero, e_end, step_e_basis, ts_eq_range, prod_e, step_e_last, step_period, kernelHom_u, kernelHom_e, forward_backward.
e (def): proof_shape: not-applicable; escape_witness: none; consumers: e_square, e_order, step, step_s, step_t, e_zero, e_end, step_e_basis, prod_e, step_e_last, step_e, step_iter_s, step_period, pref, step_s_square, pref_end, pref_square, v_pow, kernelHom_e, backL_e, back_generator, forward_ks, forward_backward.
u_zero (theorem): proof_shape: bind-only; escape_witness: none; consumers: e_zero.
u_end (theorem): proof_shape: bind-only; escape_witness: none; consumers: e_end.
u_last (theorem): proof_shape: bind-only; escape_witness: none; consumers: prod_e, step_e_last, kernelHom_u.
u_basis (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_e_basis, ts_eq_range, step_period, forward_backward.
u_square (theorem): proof_shape: bind-only; escape_witness: none; consumers: e_square.
e_square (theorem): proof_shape: bind-only; escape_witness: none; consumers: e_order, step, step_e_last, step_s_square, pref_square.
e_order (theorem): proof_shape: bind-only; escape_witness: none; consumers: step.
step (def): proof_shape: not-applicable; escape_witness: none; consumers: step_s, step_t, step_e_basis, step_e_last, step_e, step_iter_s, step_period, stepAut, stepAut_period, step_s_square, v_pow, back_generator.
step_s (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_e_basis, step_e_last, step_e, step_s_square, back_generator.
step_t (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_e_basis, step_e_last, back_generator.
e_zero (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_e, step_iter_s, pref_end, v_pow, kernelHom_e, forward_ks, forward_backward.
e_end (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_e, step_period.
step_e_basis (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_e.
ts_eq_range (theorem): proof_shape: bind-only; escape_witness: none; consumers: prod_e, step_e_last.
prod_e (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_e_last, pref_end.
step_e_last (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_e.
step_e (theorem): proof_shape: bind-only; escape_witness: none; consumers: step_iter_s, v_pow, forward_ks.
step_iter_s (theorem): proof_shape: content; escape_witness: none; consumers: step_period.
step_period (theorem): proof_shape: content; escape_witness: none; consumers: stepAut, stepAut_period.
stepAut (def): proof_shape: not-applicable; escape_witness: none; consumers: stepAut_period, alpha, alpha_generator, c_commute_r, v_pow, back_generator, back_compat, forward_ks.
stepAut_period (theorem): proof_shape: content; escape_witness: none; consumers: alpha, alpha_generator.
alpha (def): proof_shape: not-applicable; escape_witness: none; consumers: claim, alpha_generator, v, r_order, c_order, c_commute_r, c_commute_v, v_pow, v_order, rv_relation, fg, fg_relations, forward, forward_of, back_compat, backward, backward_forward, forward_ks, forward_backward, result.
claim (def): proof_shape: not-applicable; escape_witness: none; consumers: result.
alpha_generator (theorem): proof_shape: bind-only; escape_witness: none; consumers: c_commute_r, v_pow, back_compat, forward_ks.
v (def): proof_shape: not-applicable; escape_witness: none; consumers: c_commute_v, v_pow, v_order, rv_relation, fg, fg_relations, backward_forward, forward_ks, forward_backward.
pref (def): proof_shape: not-applicable; escape_witness: none; consumers: pref_end, pref_square, v_pow, v_order, rv_relation.
cg_order (theorem): proof_shape: bind-only; escape_witness: none; consumers: r_order.
r_order (theorem): proof_shape: bind-only; escape_witness: none; consumers: v_order, fg_relations.
c_order (theorem): proof_shape: bind-only; escape_witness: none; consumers: fg_relations.
step_s_square (theorem): proof_shape: bind-only; escape_witness: none; consumers: c_commute_r.
c_commute_r (theorem): proof_shape: bind-only; escape_witness: none; consumers: c_commute_v, fg_relations.
c_commute_v (theorem): proof_shape: bind-only; escape_witness: none; consumers: fg_relations.
pref_end (theorem): proof_shape: bind-only; escape_witness: none; consumers: v_order.
pref_square (theorem): proof_shape: bind-only; escape_witness: none; consumers: rv_relation.
v_pow (theorem): proof_shape: content; escape_witness: none; consumers: v_order, rv_relation.
v_order (theorem): proof_shape: content; escape_witness: none; consumers: fg_relations.
rv_relation (theorem): proof_shape: content; escape_witness: none; consumers: fg_relations.
fg (def): proof_shape: not-applicable; escape_witness: none; consumers: fg_relations, forward, forward_of, backward_forward, forward_ks, forward_backward.
fg_relations (theorem): proof_shape: content; escape_witness: none; consumers: forward, forward_of.
forward (def): proof_shape: not-applicable; escape_witness: none; consumers: forward_of, backward_forward, forward_ks, forward_backward, result.
forward_of (theorem): proof_shape: bind-only; escape_witness: none; consumers: backward_forward, forward_ks, forward_backward.
delta (def): proof_shape: not-applicable; escape_witness: none; consumers: delta_square_half, delta_square_neg, delta_square_nat, delta_square, delta_swap, delta_commute, kgens, K_isMulCommutative, kd, ks_coe, ks_square_z, ks_prod.
x_order (theorem): proof_shape: bind-only; escape_witness: none; consumers: delta_square_nat, delta_square, ks_prod, backR_cg, back_compat, backward, forward_backward.
y_order (theorem): proof_shape: bind-only; escape_witness: none; consumers: delta_square_nat, delta_square, ks_prod.
z_order (theorem): proof_shape: bind-only; escape_witness: none; consumers: delta_square_nat, delta_square, ks_order.
zx (theorem): proof_shape: bind-only; escape_witness: none; consumers: delta_square_neg.
zy (theorem): proof_shape: bind-only; escape_witness: none; consumers: delta_commute.
delta_square_half (theorem): proof_shape: bind-only; escape_witness: none; consumers: delta_square_nat.
delta_square_neg (theorem): proof_shape: bind-only; escape_witness: none; consumers: delta_square_nat.
delta_square_nat (theorem): proof_shape: bind-only; escape_witness: none; consumers: delta_square.
delta_square (theorem): proof_shape: bind-only; escape_witness: none; consumers: delta_swap, ks_square_z.
delta_swap (theorem): proof_shape: bind-only; escape_witness: none; consumers: delta_commute.
delta_commute (theorem): proof_shape: bind-only; escape_witness: none; consumers: K_isMulCommutative, ks_square_z.
kgens (def): proof_shape: not-applicable; escape_witness: none; consumers: K_isMulCommutative, kd, ks, kt, kernelHom, backL.
K_isMulCommutative (instance): proof_shape: bind-only; escape_witness: none; consumers: ks_prod, kt_square, kernelHom, kt_last, kernelHom_u, kernelHom_e.
kd (def): proof_shape: not-applicable; escape_witness: none; consumers: ks, ks_coe, ks_prod.
ks (def): proof_shape: not-applicable; escape_witness: none; consumers: ks_coe, ks_square_z, ks_square, ks_order, ks_prod, kt, kt_square, kernelHom, kernelHom_s, kernelHom_t, kt_last, kernelHom_u, kernelHom_e, backL_s, backL_e, backL_t, back_generator, backL_square, ks_succ_coe, forward_ks, forward_backward.
ks_coe (theorem): proof_shape: bind-only; escape_witness: none; consumers: backL_s, backL_e, back_generator, ks_succ_coe, forward_ks.
ks_square_z (theorem): proof_shape: bind-only; escape_witness: none; consumers: ks_square, ks_order, backL_square.
ks_square (theorem): proof_shape: bind-only; escape_witness: none; consumers: kt_square.
ks_order (theorem): proof_shape: bind-only; escape_witness: none; consumers: kernelHom, kernelHom_s, kernelHom_t.
ks_prod (theorem): proof_shape: bind-only; escape_witness: none; consumers: kt_last.
kt (def): proof_shape: not-applicable; escape_witness: none; consumers: kt_square, kernelHom, kernelHom_t, kt_last, kernelHom_u, kernelHom_e, backL_t.
kt_square (theorem): proof_shape: bind-only; escape_witness: none; consumers: kernelHom, kt_last.
kernelHom (def): proof_shape: not-applicable; escape_witness: none; consumers: kernelHom_s, kernelHom_t, kernelHom_u, kernelHom_e, backL, backL_s, backL_e, backL_t, backL_square.
kernelHom_s (theorem): proof_shape: bind-only; escape_witness: none; consumers: kernelHom_u, kernelHom_e, backL_s, backL_square.
kernelHom_t (theorem): proof_shape: bind-only; escape_witness: none; consumers: kernelHom_u, backL_t.
kt_last (theorem): proof_shape: bind-only; escape_witness: none; consumers: kernelHom_u.
kernelHom_u (theorem): proof_shape: bind-only; escape_witness: none; consumers: kernelHom_e.
kernelHom_e (theorem): proof_shape: bind-only; escape_witness: none; consumers: backL_e.
backL (def): proof_shape: not-applicable; escape_witness: none; consumers: backL_s, backL_e, backL_t, back_generator, back_compat, backward, backL_square, backward_forward, forward_backward.
backL_s (theorem): proof_shape: bind-only; escape_witness: none; consumers: back_generator, backward_forward, forward_backward.
backL_e (theorem): proof_shape: bind-only; escape_witness: none; consumers: back_generator.
backL_t (theorem): proof_shape: bind-only; escape_witness: none; consumers: back_generator, forward_backward.
backR_cg (theorem): proof_shape: bind-only; escape_witness: none; consumers: back_compat, forward_backward.
back_generator (theorem): proof_shape: bind-only; escape_witness: none; consumers: back_compat.
back_compat (theorem): proof_shape: content; escape_witness: none; consumers: backward, backward_forward, forward_backward.
backward (def): proof_shape: not-applicable; escape_witness: none; consumers: backward_forward, forward_backward, result.
backL_square (theorem): proof_shape: bind-only; escape_witness: none; consumers: backward_forward.
backward_forward (theorem): proof_shape: bind-only; escape_witness: none; consumers: result.
ks_succ_coe (theorem): proof_shape: bind-only; escape_witness: none; consumers: forward_ks.
forward_ks (theorem): proof_shape: content; escape_witness: none; consumers: forward_backward.
forward_backward (theorem): proof_shape: content; escape_witness: none; consumers: result.
result (theorem): proof_shape: content; escape_witness: none; consumers: none.
Module admission_basis: open-problem-resolution (#16204; Proved).
Direct frozen dependencies: none (pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16351.
Escape audit for cyclicHom_int unfinished: https://github.com/the-omega-institute/trureturing/issues/19215.
The utility is none: this is a uniform structural theorem, not a finite computation.
The cyclic and product maps use ZMod.lift, zmultiplesHom, noncommCoprod and
noncommPiCoprod; homomorphism extensionality uses the upstream generator theorem.
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Algebra.BigOperators.Fin
open scoped commutatorElement
open Multiplicative
open Finset
namespace D5.S3.Quantum.Algebra.GeneralizedCHSHGroupDecomposition
abbrev P0 : FreeGroup (Fin 3) := FreeGroup.of 0
abbrev P1 : FreeGroup (Fin 3) := FreeGroup.of 1
abbrev J : FreeGroup (Fin 3) := FreeGroup.of 2
def rels (n : ℕ) : Set (FreeGroup (Fin 3)) :=
  {P0 ^ n, P1 ^ n, J ^ n, ⁅J, P0⁆, ⁅J, P1⁆} ∪
  {r | ∃ i : ℕ, 1 ≤ i ∧ i ≤ n / 2 ∧
    r = J ^ i * (P0 ^ i * P1 ^ (-(i : ℤ))) ^ 2}
abbrev G (n : ℕ) := PresentedGroup (rels n)
abbrev L (n : ℕ) := Multiplicative (ZMod (2 * n)) ×
  (Fin (n - 2) → Multiplicative (ZMod 2))

noncomputable def cyclicHom {H : Type*} [Group H] (n : ℕ) (a : H) (ha : a ^ n = 1) :
    Multiplicative (ZMod n) →* H :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift n
    ⟨zmultiplesHom (Additive H) (Additive.ofMul a), by
      change a ^ (n : ℤ) = 1
      simpa only [zpow_natCast] using ha⟩)

@[simp] theorem cyclicHom_int {H : Type*} [Group H] (n : ℕ) (a : H) (ha)
    (i : ℤ) : cyclicHom n a ha (ofAdd (i : ZMod n)) = a ^ i := by
  unfold cyclicHom
  change Additive.toMul ((ZMod.lift n _) (i : ZMod n)) = _
  rw [ZMod.lift_coe]
  rfl
@[simp] private theorem cyclicHom_one {H : Type*} [Group H] (n : ℕ) (a : H) (ha) :
    cyclicHom n a ha (ofAdd (1 : ZMod n)) = a := by
  simpa using cyclicHom_int n a ha 1

private theorem cyclicHom_ext {H : Type*} [Group H] {n : ℕ}
    (f g : Multiplicative (ZMod n) →* H)
    (h : f (ofAdd (1 : ZMod n)) = g (ofAdd (1 : ZMod n))) : f = g := by
  apply (MonoidHom.eq_iff_eq_on_generator (g := ofAdd (1 : ZMod n))
    (fun x => by
      obtain ⟨i, hi⟩ := ZMod.intCast_surjective x.toAdd
      refine ⟨i, ?_⟩
      change ofAdd (i • (1 : ZMod n)) = x
      simpa using congrArg ofAdd hi) f g).mpr h

def s (n : ℕ) : L n := (ofAdd 1, 1)
def t (n : ℕ) (i : Fin (n - 2)) : L n := (1, Pi.mulSingle i (ofAdd 1))

@[simp] private theorem s_order (n : ℕ) : s n ^ (2*n) = 1 := by
  apply Prod.ext
  · change (2*n) • (1 : ZMod (2*n)) = 0
    simp
  · funext j
    simp [s]
@[simp] private theorem t_square (n : ℕ) (i : Fin (n-2)) : t n i ^ 2 = 1 := by
  apply Prod.ext
  · simp [t]
  · funext j
    by_cases h : j = i
    · subst j
      simp [t, Pi.mulSingle_eq_same]
      rfl
    · simp [t, Pi.mulSingle_eq_of_ne h]

noncomputable def liftL {H : Type*} [Group H] (n : ℕ) (a : H)
    (b : Fin (n-2) → H) (ha : a ^ (2*n) = 1) (hb : ∀ i, b i ^ 2 = 1)
    (hc : ∀ i j, Commute (b i) (b j)) (hd : ∀ i, Commute a (b i)) : L n →* H :=
  MonoidHom.noncommCoprod (cyclicHom (2*n) a ha)
    (MonoidHom.noncommPiCoprod (fun i => cyclicHom 2 (b i) (hb i)) (by
      intro i j hij x y
      obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
      obtain ⟨l, hl⟩ := ZMod.intCast_surjective y.toAdd
      have hx : x = ofAdd (k : ZMod 2) := congrArg ofAdd hk.symm
      have hy : y = ofAdd (l : ZMod 2) := congrArg ofAdd hl.symm
      simp only [hx, hy, cyclicHom_int]
      exact (hc i j).zpow_zpow k l)) (by
      intro x y
      obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
      have hx : x = ofAdd (k : ZMod (2*n)) := congrArg ofAdd hk.symm
      rw [hx, cyclicHom_int]
      simp only [MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]
      apply Finset.noncommProd_commute
      intro i hi
      obtain ⟨l, hl⟩ := ZMod.intCast_surjective (y i).toAdd
      have hy : y i = ofAdd (l : ZMod 2) := congrArg ofAdd hl.symm
      simp only [hy, cyclicHom_int]
      exact (hd i).zpow_zpow k l)

@[simp] private theorem liftL_s {H : Type*} [Group H] (n : ℕ) (a : H) (b) (ha hb hc hd) :
    liftL n a b ha hb hc hd (s n) = a := by
  simp [liftL, s]
set_option backward.isDefEq.respectTransparency false in
@[simp] private theorem liftL_t {H : Type*} [Group H] (n : ℕ) (a : H) (b) (ha hb hc hd)
    (i : Fin (n-2)) : liftL n a b ha hb hc hd (t n i) = b i := by
  simp only [liftL, t, MonoidHom.noncommCoprod_apply, map_one, one_mul]
  simp only [MonoidHom.noncommPiCoprod_mulSingle, cyclicHom_one]

private theorem L_hom_ext {H : Type*} [Group H] {n : ℕ} (f g : L n →* H)
    (hs : f (s n) = g (s n)) (ht : ∀ i, f (t n i) = g (t n i)) : f = g := by
  have h1 : f.comp (MonoidHom.inl _ _) = g.comp (MonoidHom.inl _ _) :=
    cyclicHom_ext _ _ hs
  have h2 : f.comp (MonoidHom.inr _ _) = g.comp (MonoidHom.inr _ _) := by
    apply MonoidHom.pi_ext
    intro i x
    have hh := congrArg (fun p : Multiplicative (ZMod 2) →* H => p x)
      (cyclicHom_ext (f.comp ((MonoidHom.inr _ _).comp (MonoidHom.mulSingle (fun _ : Fin (n-2) => Multiplicative (ZMod 2)) i)))
        (g.comp ((MonoidHom.inr _ _).comp (MonoidHom.mulSingle (fun _ : Fin (n-2) => Multiplicative (ZMod 2)) i))) (ht i))
    exact hh
  apply DFunLike.ext
  intro x
  have hx : x = (x.1, 1) * (1, x.2) := by ext <;> simp
  rw [hx, map_mul, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun h1 x.1) (DFunLike.congr_fun h2 x.2)

def ts (n : ℕ) : L n := ∏ i, t n i
@[simp] private theorem ts_square (n : ℕ) : ts n ^ 2 = 1 := by
  simp only [ts, ← Finset.prod_pow, t_square, Finset.prod_const_one]

def u (n k : ℕ) : L n :=
  if hk : 1 ≤ k ∧ k ≤ n - 2 then t n ⟨k - 1, by omega⟩
  else if k = n - 1 then s n ^ n * ts n else 1

def e (n k : ℕ) : L n := s n * u n k

@[simp] private theorem u_zero (n : ℕ) (hn : 2 ≤ n) : u n 0 = 1 := by
  simp [u, show 0 ≠ n-1 by omega]
@[simp] private theorem u_end (n : ℕ) (hn : 2 ≤ n) : u n n = 1 := by
  simp [u, show ¬(1 ≤ n ∧ n ≤ n-2) by omega, show n ≠ n-1 by omega]
@[simp] private theorem u_last (n : ℕ) (hn : 2 ≤ n) : u n (n-1) = s n ^ n * ts n := by
  rw [u, dif_neg (by omega), if_pos rfl]
@[simp] private theorem u_basis (n : ℕ) (i : Fin (n-2)) : u n (i.val+1) = t n i := by
  simp [u, show 1 ≤ i.val+1 ∧ i.val+1 ≤ n-2 by omega]
@[simp] private theorem u_square (n k : ℕ) : u n k ^ 2 = 1 := by
  unfold u
  split
  · exact t_square n _
  · split
    · rw [mul_pow, ts_square, mul_one, ← pow_mul]
      simpa [Nat.mul_comm] using s_order n
    · simp
@[simp] private theorem e_square (n k : ℕ) : e n k ^ 2 = s n ^ 2 := by
  simp [e, mul_pow]
@[simp] private theorem e_order (n k : ℕ) : e n k ^ (2*n) = 1 := by
  rw [pow_mul, e_square, ← pow_mul, s_order]

noncomputable def step (n : ℕ) : L n →* L n :=
  liftL n (e n 1) (fun i => e n (i.val+2) * (e n 1)⁻¹)
    (e_order n 1) (fun i => by simp [mul_pow, inv_pow])
    (fun _ _ => Commute.all _ _) (fun _ => Commute.all _ _)

@[simp] private theorem step_s (n : ℕ) : step n (s n) = e n 1 := liftL_s ..
@[simp] private theorem step_t (n : ℕ) (i : Fin (n-2)) :
    step n (t n i) = e n (i.val+2) * (e n 1)⁻¹ := liftL_t ..
@[simp] private theorem e_zero (n : ℕ) (hn : 2 ≤ n) : e n 0 = s n := by simp [e, hn]
@[simp] private theorem e_end (n : ℕ) (hn : 2 ≤ n) : e n n = s n := by simp [e, hn]
@[simp] private theorem step_e_basis (n : ℕ) (i : Fin (n-2)) :
    step n (e n (i.val+1)) = e n (i.val+2) := by
  rw [e, u_basis, map_mul, step_s, step_t]
  simp

private theorem ts_eq_range (n : ℕ) : ts n = ∏ i ∈ range (n-2), u n (i+1) := by
  rw [← Fin.prod_univ_eq_prod_range]
  simp [ts]

private theorem prod_e (n : ℕ) (hn : 2 ≤ n) :
    (∏ i ∈ range (n-1), e n (i+1)) = (s n)⁻¹ := by
  have har : n-1 = (n-2)+1 := by omega
  have hinit : (∏ i ∈ range (n-2), e n (i+1)) = s n ^ (n-2) * ts n := by
    simp only [e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [← ts_eq_range]
  apply eq_inv_iff_mul_eq_one.mpr
  rw [har, Finset.prod_range_succ, hinit]
  rw [show n-2+1 = n-1 by omega, e, u_last n hn]
  calc
    s n ^ (n-2) * ts n * (s n * (s n ^ n * ts n)) * s n =
        s n ^ ((n-2)+n+2) * ts n ^ 2 := by
      simp only [pow_add, pow_two]; ac_rfl
    _ = 1 := by rw [show (n-2)+n+2 = 2*n by omega, s_order, ts_square, mul_one]

private theorem step_e_last (n : ℕ) (hn : 2 ≤ n) : step n (e n (n-1)) = s n := by
  have htail : e n 1 * (∏ i ∈ range (n-2), e n (i+2)) = (s n)⁻¹ := by
    have h := prod_e n hn
    rw [show n-1=(n-2)+1 by omega, Finset.prod_range_succ'] at h
    simpa [Nat.add_assoc, mul_comm] using h
  have hts : step n (ts n) =
      (∏ i ∈ range (n-2), e n (i+2)) * ((e n 1)⁻¹) ^ (n-2) := by
    rw [ts_eq_range, map_prod]
    have hh : ∀ i ∈ range (n-2), step n (u n (i+1)) = e n (i+2) * (e n 1)⁻¹ := by
      intro i hi
      have hi' : i < n-2 := mem_range.mp hi
      rw [u, dif_pos (by omega)]
      exact step_t n ⟨i, hi'⟩
    rw [prod_congr rfl hh, Finset.prod_mul_distrib]
    simp
  rw [e, u_last n hn, map_mul, map_mul, map_pow, step_s, hts]
  have hp : n = (n-2)+2 := by omega
  calc
    e n 1 * (e n 1 ^ n * ((∏ i ∈ range (n-2), e n (i+2)) *
        (e n 1)⁻¹ ^ (n-2))) = e n 1 ^ 2 *
        (e n 1 * (∏ i ∈ range (n-2), e n (i+2))) := by
      have hpow : e n 1 ^ n = e n 1 ^ (n-2) * e n 1 ^ 2 := by
        rw [← pow_add, ← hp]
      rw [hpow, inv_pow]
      simp only [pow_two]
      calc
        _ = (e n 1 ^ (n-2) * (e n 1 ^ (n-2))⁻¹) *
            (e n 1 * e n 1 * (e n 1 * ∏ i ∈ range (n-2), e n (i+2))) := by ac_rfl
        _ = _ := by rw [mul_inv_cancel, one_mul]
    _ = s n := by rw [e_square, htail]; group

private theorem step_e (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k < n) :
    step n (e n k) = e n (k+1) := by
  by_cases h0 : k = 0
  · subst k; simp [hn]
  by_cases hlast : k = n-1
  · subst k
    rw [step_e_last n hn, show n-1+1=n by omega, e_end n hn]
  have hi : k-1 < n-2 := by omega
  have h := step_e_basis n ⟨k-1, hi⟩
  simpa only [show k-1+1=k by omega, show k-1+2=k+1 by omega] using h

private theorem step_iter_s (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k ≤ n) :
    (step n)^[k] (s n) = e n k := by
  induction k with
  | zero => simp [hn]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega), step_e n hn k (by omega)]

private theorem step_period (n : ℕ) (hn : 2 ≤ n) : (step n)^[n] = id := by
  have hs : (step n)^[n] (s n) = s n := by rw [step_iter_s n hn n le_rfl, e_end n hn]
  let f : L n →* L n :=
    { toFun := (step n)^[n], map_one' := iterate_map_one (step n) n,
      map_mul' := iterate_map_mul (step n) n }
  have hgen (k : ℕ) (hk : k ≤ n) : (step n)^[n] (e n k) = e n k := by
    rw [← step_iter_s n hn k hk, ← Function.iterate_add_apply, Nat.add_comm n k, Function.iterate_add_apply, hs]
  have ht (i : Fin (n-2)) : (step n)^[n] (t n i) = t n i := by
    have hb : t n i = e n (i.val+1) * (s n)⁻¹ := by simp [e]
    rw [hb, iterate_map_mul, iterate_map_inv, hs, hgen (i.val+1) (by omega)]
  have hf : f = MonoidHom.id (L n) := L_hom_ext f _ hs ht
  exact congrArg (fun h : L n →* L n => (h : L n → L n)) hf

noncomputable def stepAut (n : ℕ) (hn : 2 ≤ n) : MulAut (L n) where
  toFun := step n
  invFun := (step n)^[n-1]
  left_inv x := by
    rw [← Function.iterate_succ_apply, show (n-1).succ=n by omega, step_period n hn]
    rfl
  right_inv x := by
    rw [← Function.iterate_succ_apply' (step n) (n-1) x, show (n-1).succ=n by omega, step_period n hn]
    rfl
  map_mul' := map_mul (step n)

private theorem stepAut_period (n : ℕ) (hn : 2 ≤ n) : stepAut n hn ^ n = 1 := by
  have hcoe (k : ℕ) : ⇑(stepAut n hn ^ k) = (step n)^[k] := by
    change ⇑(MulAut.toPerm (L n) (stepAut n hn ^ k)) = _
    rw [map_pow, Equiv.Perm.coe_pow]
    rfl
  apply DFunLike.ext
  intro x
  rw [hcoe, step_period n hn]
  rfl

noncomputable def alpha (n : ℕ) : Multiplicative (ZMod n) →* MulAut (L n) :=
  if hn : 2 ≤ n then cyclicHom n (stepAut n hn) (stepAut_period n hn) else 1

def claim : Prop := ∀ n : ℕ, 2 ≤ n →
  Nonempty (G n ≃* L n ⋊[alpha n] Multiplicative (ZMod n))

private theorem alpha_generator (n : ℕ) (hn : 2 ≤ n) : alpha n (ofAdd 1) = stepAut n hn := by
  simp only [alpha, dif_pos hn, cyclicHom_one]

noncomputable section

private def v (n : ℕ) : (L n ⋊[alpha n] Multiplicative (ZMod n)) := SemidirectProduct.inl (s n) * (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n))
private def pref (n k : ℕ) : L n := ∏ i ∈ range k, e n i

@[simp] private theorem cg_order (n : ℕ) : (ofAdd (1 : ZMod n)) ^ n = 1 := by
  change n • (1 : ZMod n) = 0
  simp
@[simp] private theorem r_order (n : ℕ) : (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ n = 1 := by simp [← map_pow]
@[simp] private theorem c_order (n : ℕ) : (SemidirectProduct.inl (s n ^ 2) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ n = 1 := by
  rw [← map_pow, ← pow_mul, s_order, map_one]

private theorem step_s_square (n : ℕ) : step n (s n ^ 2) = s n ^ 2 := by
  rw [map_pow, step_s, e_square]

private theorem c_commute_r (n : ℕ) (hn : 2 ≤ n) : Commute ((SemidirectProduct.inl (s n ^ 2) : L n ⋊[alpha n] Multiplicative (ZMod n))) ((SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n))) := by
  have hh : alpha n ((ofAdd (1 : ZMod n))) (s n ^ 2) = s n ^ 2 := by
    rw [alpha_generator n hn]; exact step_s_square n
  change (SemidirectProduct.inl (s n ^ 2) : L n ⋊[alpha n] Multiplicative (ZMod n)) * (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) = (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) * (SemidirectProduct.inl (s n ^ 2) : L n ⋊[alpha n] Multiplicative (ZMod n))
  apply SemidirectProduct.ext <;> simp [hh, -map_pow]

private theorem c_commute_v (n : ℕ) (hn : 2 ≤ n) : Commute ((SemidirectProduct.inl (s n ^ 2) : L n ⋊[alpha n] Multiplicative (ZMod n))) (v n) := by
  apply Commute.mul_right _ (c_commute_r n hn)
  exact (Commute.all (s n ^ 2) (s n)).map SemidirectProduct.inl

private theorem pref_end (n : ℕ) (hn : 2 ≤ n) : pref n n = 1 := by
  unfold pref
  conv_lhs => arg 1; rw [show n=(n-1)+1 by omega]
  rw [Finset.prod_range_succ', e_zero n hn, prod_e n hn, inv_mul_cancel]

private theorem pref_square (n k : ℕ) : pref n k ^ 2 = s n ^ (2*k) := by
  simp only [pref, ← Finset.prod_pow, e_square, Finset.prod_const,
    Finset.card_range, ← pow_mul]

private theorem v_pow (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k ≤ n) :
    v n ^ k = SemidirectProduct.inl (pref n k) * (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ k := by
  induction k with
  | zero => simp [pref]
  | succ k ih =>
    have hrot : alpha n ((ofAdd (1 : ZMod n))) (pref n k) =
        ∏ i ∈ range k, e n (i+1) := by
      rw [alpha_generator n hn]
      change step n (pref n k) = _
      rw [pref, map_prod]
      apply prod_congr rfl
      intro i hi
      exact step_e n hn i (by have := mem_range.mp hi; omega)
    have hconj : (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) * SemidirectProduct.inl (pref n k) =
        SemidirectProduct.inl (alpha n ((ofAdd (1 : ZMod n))) (pref n k)) * (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) := by
      ext <;> simp []
    rw [pow_succ', ih (by omega), v]
    calc
      SemidirectProduct.inl (s n) * (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) *
          (SemidirectProduct.inl (pref n k) * (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ k) =
          SemidirectProduct.inl (s n) * ((SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) * SemidirectProduct.inl (pref n k)) * (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ k := by group
      _ = SemidirectProduct.inl (s n * (∏ i ∈ range k, e n (i+1))) * (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ (k+1) := by
        rw [hconj, hrot, map_mul, pow_succ']; group
      _ = SemidirectProduct.inl (pref n (k+1)) * (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ (k+1) := by
        congr 2
        simp only [pref, Finset.prod_range_succ', e_zero n hn]
        rw [mul_comm]

@[simp] private theorem v_order (n : ℕ) (hn : 2 ≤ n) : v n ^ n = 1 := by
  rw [v_pow n hn n le_rfl, pref_end n hn, map_one, r_order, mul_one]

private theorem rv_relation (n : ℕ) (hn : 2 ≤ n) (i : ℕ) (hi : i ≤ n) :
    (SemidirectProduct.inl (s n ^ 2) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ i * ((SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ i * v n ^ (-(i : ℤ))) ^ 2 = 1 := by
  have h : (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ i * v n ^ (-(i : ℤ)) = SemidirectProduct.inl ((pref n i)⁻¹) := by
    rw [zpow_neg, zpow_natCast, v_pow n hn i hi, map_inv]
    group
  rw [h, ← map_pow, ← map_pow, ← map_mul]
  have hh : (s n ^ 2) ^ i * ((pref n i)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, pref_square, ← pow_mul]
    exact mul_inv_cancel _
  rw [hh, map_one]

private def fg (n : ℕ) : Fin 3 → (L n ⋊[alpha n] Multiplicative (ZMod n)) := ![(SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)), v n, (SemidirectProduct.inl (s n ^ 2) : L n ⋊[alpha n] Multiplicative (ZMod n))]

private theorem fg_relations (n : ℕ) (hn : 2 ≤ n) :
    ∀ w ∈ rels n, FreeGroup.lift (fg n) w = 1 := by
  intro w hw
  rcases hw with hw | hw
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · simp [P0, fg]
    · simp [P1, fg, v_order n hn]
    · simp only [J, map_pow, FreeGroup.lift_apply_of]
      change (SemidirectProduct.inl (s n ^ 2) : L n ⋊[alpha n] Multiplicative (ZMod n)) ^ n = 1
      exact c_order n
    · simp only [map_commutatorElement, FreeGroup.lift_apply_of, fg, P0, J,
        Matrix.cons_val_zero, Matrix.cons_val_two]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (c_commute_r n hn).eq
    · simp only [map_commutatorElement, FreeGroup.lift_apply_of, fg, P1, J,
        Matrix.cons_val_one, Matrix.cons_val_two]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (c_commute_v n hn).eq
  · rcases hw with ⟨i, hi, hn', rfl⟩
    simpa [fg, P0, P1, J] using rv_relation n hn i (by omega)

private noncomputable def forward (n : ℕ) (hn : 2 ≤ n) : G n →* (L n ⋊[alpha n] Multiplicative (ZMod n)) :=
  PresentedGroup.toGroup (fg_relations n hn)

@[simp] private theorem forward_of (n : ℕ) (hn : 2 ≤ n) (i : Fin 3) :
    forward n hn (PresentedGroup.of i) = fg n i := PresentedGroup.toGroup.of _


private def delta (n : ℕ) (i : ℤ) : G n := (PresentedGroup.of (rels := rels n) 0) ^ i * (PresentedGroup.of (rels := rels n) 1) ^ (-i)

@[simp] private theorem x_order (n : ℕ) : (PresentedGroup.of (rels := rels n) 0) ^ n = 1 := by
  have h := PresentedGroup.one_of_mem (rels := rels n) (x := P0 ^ n) (by simp [rels])
  simpa [PresentedGroup.of] using h
@[simp] private theorem y_order (n : ℕ) : (PresentedGroup.of (rels := rels n) 1) ^ n = 1 := by
  have h := PresentedGroup.one_of_mem (rels := rels n) (x := P1 ^ n) (by simp [rels])
  simpa [PresentedGroup.of] using h
@[simp] private theorem z_order (n : ℕ) : (PresentedGroup.of (rels := rels n) 2) ^ n = 1 := by
  have h := PresentedGroup.one_of_mem (rels := rels n) (x := J ^ n) (by simp [rels])
  simpa [PresentedGroup.of] using h

private theorem zx (n : ℕ) : Commute ((PresentedGroup.of (rels := rels n) 2)) ((PresentedGroup.of (rels := rels n) 0)) := by
  have h := PresentedGroup.one_of_mem (rels := rels n) (x := ⁅J, P0⁆) (by simp [rels])
  apply commutatorElement_eq_one_iff_mul_comm.mp
  simpa [PresentedGroup.of] using h

private theorem zy (n : ℕ) : Commute ((PresentedGroup.of (rels := rels n) 2)) ((PresentedGroup.of (rels := rels n) 1)) := by
  have h := PresentedGroup.one_of_mem (rels := rels n) (x := ⁅J, P1⁆) (by simp [rels])
  apply commutatorElement_eq_one_iff_mul_comm.mp
  simpa [PresentedGroup.of] using h

private theorem delta_square_half (n i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ n/2) :
    delta n (i : ℤ) ^ 2 = (PresentedGroup.of (rels := rels n) 2) ^ (-(i : ℤ)) := by
  have hm : J ^ i * (P0 ^ i * P1 ^ (-(i : ℤ))) ^ 2 ∈ rels n :=
    Or.inr ⟨i, hi, hi', rfl⟩
  have h := PresentedGroup.one_of_mem hm
  have hh : (PresentedGroup.of (rels := rels n) 2) ^ i * delta n (i : ℤ) ^ 2 = 1 := by
    simpa [delta, PresentedGroup.of] using h
  simpa only [zpow_neg, zpow_natCast] using eq_inv_of_mul_eq_one_right hh

private theorem delta_square_neg (n : ℕ) (i : ℤ)
    (hi : delta n i ^ 2 = (PresentedGroup.of (rels := rels n) 2) ^ (-i)) : delta n (-i) ^ 2 = (PresentedGroup.of (rels := rels n) 2) ^ i := by
  calc
    delta n (-i) ^ 2 = (PresentedGroup.of (rels := rels n) 0) ^ (-i) * (delta n i ^ 2)⁻¹ * (PresentedGroup.of (rels := rels n) 0) ^ i := by
      dsimp [delta]; simp only [pow_two, mul_inv_rev]; group
    _ = (PresentedGroup.of (rels := rels n) 0) ^ (-i) * (PresentedGroup.of (rels := rels n) 2) ^ i * (PresentedGroup.of (rels := rels n) 0) ^ i := by rw [hi]; simp
    _ = (PresentedGroup.of (rels := rels n) 2) ^ i := by rw [((zx n).zpow_zpow i (-i)).symm.eq]; group

private theorem delta_square_nat (n : ℕ) (hn : 2 ≤ n) (i : ℕ) (hi : i < n) :
    delta n (i : ℤ) ^ 2 = (PresentedGroup.of (rels := rels n) 2) ^ (-(i : ℤ)) := by
  by_cases h0 : i = 0
  · subst i; simp [delta]
  by_cases hh : i ≤ n/2
  · exact delta_square_half n i (by omega) hh
  have hk : 1 ≤ n-i ∧ n-i ≤ n/2 := by omega
  have h := delta_square_neg n (n-i : ℕ)
    (delta_square_half n (n-i) hk.1 hk.2)
  have hper {H : Type} [Group H] (a : H) (ha : a ^ n = 1) :
      a ^ (i : ℤ) = a ^ (-(n-i : ℕ) : ℤ) := by
    have hi' : (i : ℤ) = (n : ℤ) - (n-i : ℕ) := by omega
    rw [hi', zpow_sub, zpow_natCast, ha, one_mul, zpow_neg]
  rw [delta]
  simp only [zpow_neg]
  rw [hper ((PresentedGroup.of (rels := rels n) 0)) (x_order n), hper ((PresentedGroup.of (rels := rels n) 1)) (y_order n), hper ((PresentedGroup.of (rels := rels n) 2)) (z_order n)]
  simpa [delta, zpow_neg] using h

private theorem delta_square (n : ℕ) (hn : 2 ≤ n) (i : ℤ) :
    delta n i ^ 2 = (PresentedGroup.of (rels := rels n) 2) ^ (-i) := by
  let k := (i % (n : ℤ)).toNat
  have hk0 : 0 ≤ i % (n : ℤ) := Int.emod_nonneg _ (by omega)
  have hk : k < n := by
    have := Int.emod_lt_of_pos i (show 0 < (n : ℤ) by omega)
    dsimp [k]; omega
  have hper {H : Type} [Group H] (a : H) (ha : a ^ n = 1) :
      a ^ i = a ^ (k : ℤ) := by
    rw [zpow_eq_zpow_emod' i ha]
    congr 1
    exact (Int.toNat_of_nonneg hk0).symm
  simp only [delta, zpow_neg, hper ((PresentedGroup.of (rels := rels n) 0)) (x_order n), hper ((PresentedGroup.of (rels := rels n) 1)) (y_order n), hper ((PresentedGroup.of (rels := rels n) 2)) (z_order n)]
  simpa only [delta, zpow_neg] using delta_square_nat n hn k hk

private theorem delta_swap (n : ℕ) (hn : 2 ≤ n) (i : ℤ) :
    delta n i = (PresentedGroup.of (rels := rels n) 2) ^ (-i) * (PresentedGroup.of (rels := rels n) 1) ^ i * (PresentedGroup.of (rels := rels n) 0) ^ (-i) := by
  calc
    delta n i = delta n i ^ 2 * (delta n i)⁻¹ := by group
    _ = _ := by rw [delta_square n hn i]; dsimp [delta]; group

private theorem delta_commute (n : ℕ) (hn : 2 ≤ n) (i j : ℤ) :
    Commute (delta n i) (delta n j) := by
  change delta n i * delta n j = delta n j * delta n i
  calc
    delta n i * delta n j =
        (PresentedGroup.of (rels := rels n) 2) ^ (-i) * (PresentedGroup.of (rels := rels n) 1) ^ i * delta n (j-i) * (PresentedGroup.of (rels := rels n) 1) ^ (-i) := by
      rw [delta_swap n hn i]; dsimp [delta]; group
    _ = (PresentedGroup.of (rels := rels n) 2) ^ (-i) * (PresentedGroup.of (rels := rels n) 1) ^ i * ((PresentedGroup.of (rels := rels n) 2) ^ (-(j-i)) * (PresentedGroup.of (rels := rels n) 1) ^ (j-i) * (PresentedGroup.of (rels := rels n) 0) ^ (-(j-i))) * (PresentedGroup.of (rels := rels n) 1) ^ (-i) := by
      rw [delta_swap n hn (j-i)]
    _ = (PresentedGroup.of (rels := rels n) 2) ^ (-j) * (PresentedGroup.of (rels := rels n) 1) ^ j * (PresentedGroup.of (rels := rels n) 0) ^ (-j) * delta n i := by
      have hc := (zy n).zpow_zpow (-(j-i)) i
      calc
        _ = (PresentedGroup.of (rels := rels n) 2) ^ (-i) * ((PresentedGroup.of (rels := rels n) 1) ^ i * (PresentedGroup.of (rels := rels n) 2) ^ (-(j-i))) * (PresentedGroup.of (rels := rels n) 1) ^ (j-i) * (PresentedGroup.of (rels := rels n) 0) ^ (-(j-i)) * (PresentedGroup.of (rels := rels n) 1) ^ (-i) := by group
        _ = _ := by rw [hc.symm.eq]; dsimp [delta]; group
    _ = delta n j * delta n i := by rw [← delta_swap n hn j]


private def kgens (n : ℕ) : Set (G n) := if 2 ≤ n then Set.range (delta n) else {1}
private instance K_isMulCommutative (n : ℕ) : IsMulCommutative ((Subgroup.closure (kgens n))) := by
  apply Subgroup.isMulCommutative_closure
  intro a ha b hb _
  by_cases hn : 2 ≤ n
  · simp only [kgens, if_pos hn, Set.mem_range] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact delta_commute n hn i j
  · simp only [kgens, if_neg hn, Set.mem_singleton_iff] at ha hb
    simp [ha, hb]
open scoped IsMulCommutative

private def kd (n : ℕ) (hn : 2 ≤ n) (i : ℤ) : (Subgroup.closure (kgens n)) :=
  ⟨delta n i, Subgroup.subset_closure (by simp only [kgens, if_pos hn]; exact ⟨i, rfl⟩)⟩
private def ks (n : ℕ) (hn : 2 ≤ n) (i : ℤ) : (Subgroup.closure (kgens n)) := kd n hn i * (kd n hn (i+1))⁻¹

private theorem ks_coe (n : ℕ) (hn : 2 ≤ n) (i : ℤ) :
    (ks n hn i : G n) = (PresentedGroup.of (rels := rels n) 0) ^ i * (PresentedGroup.of (rels := rels n) 1) * (PresentedGroup.of (rels := rels n) 0) ^ (-(i+1)) := by
  dsimp [ks, kd, delta]
  group

private theorem ks_square_z (n : ℕ) (hn : 2 ≤ n) (i : ℤ) :
    (ks n hn i : G n) ^ 2 = (PresentedGroup.of (rels := rels n) 2) := by
  change (delta n i * (delta n (i+1))⁻¹) ^ 2 = _
  rw [((delta_commute n hn i (i+1)).inv_right).mul_pow,
    inv_pow, delta_square n hn i, delta_square n hn (i+1)]
  group

private theorem ks_square (n : ℕ) (hn : 2 ≤ n) (i : ℤ) :
    ks n hn i ^ 2 = ks n hn 0 ^ 2 := by
  apply Subtype.ext
  exact (ks_square_z n hn i).trans (ks_square_z n hn 0).symm

private theorem ks_order (n : ℕ) (hn : 2 ≤ n) : ks n hn 0 ^ (2*n) = 1 := by
  apply Subtype.ext
  change (ks n hn 0 : G n) ^ (2*n) = 1
  rw [pow_mul, ks_square_z, z_order]

private theorem ks_prod (n : ℕ) (hn : 2 ≤ n) : (∏ i ∈ range n, ks n hn i) = 1 := by
  simp only [ks, ← div_eq_mul_inv, ← Int.natCast_add, ← Int.natCast_one]
  rw [Finset.prod_range_div']
  apply Subtype.ext
  simp [kd, delta, x_order, y_order]

private def kt (n : ℕ) (hn : 2 ≤ n) (i : ℕ) : (Subgroup.closure (kgens n)) := ks n hn i * (ks n hn 0)⁻¹
@[simp] private theorem kt_square (n : ℕ) (hn : 2 ≤ n) (i : ℕ) : kt n hn i ^ 2 = 1 := by
  rw [kt, mul_pow, inv_pow, ks_square]
  simp

private noncomputable def kernelHom (n : ℕ) (hn : 2 ≤ n) : L n →* (Subgroup.closure (kgens n)) :=
  liftL n (ks n hn 0) ((fun i : Fin (n-2) => kt n hn (i.val+1))) (ks_order n hn) (fun i => kt_square n hn _)
    (fun _ _ => Commute.all _ _) (fun _ => Commute.all _ _)

@[simp] private theorem kernelHom_s (n : ℕ) (hn : 2 ≤ n) : kernelHom n hn (s n) = ks n hn 0 := liftL_s ..
@[simp] private theorem kernelHom_t (n : ℕ) (hn : 2 ≤ n) (i : Fin (n-2)) :
    kernelHom n hn (t n i) = kt n hn (i.val+1) := liftL_t ..


private theorem kt_last (n : ℕ) (hn : 2 ≤ n) :
    kt n hn (n-1) = ks n hn 0 ^ n * ∏ i : Fin (n-2), (fun i : Fin (n-2) => kt n hn (i.val+1)) i := by
  have hp : ks n hn 0 * (∏ i ∈ range (n-1), ks n hn (i+1)) = 1 := by
    have h := ks_prod n hn
    conv_lhs at h => arg 1; rw [show n=(n-1)+1 by omega]
    rw [Finset.prod_range_succ'] at h
    simpa [mul_comm, Nat.cast_add, Nat.cast_one] using h
  have hall : ks n hn 0 ^ n * (∏ i ∈ range (n-1), kt n hn (i+1)) = 1 := by
    simp only [kt, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, inv_pow]
    have hn' : ks n hn 0 ^ n = ks n hn 0 ^ (n-1) * ks n hn 0 := by
      rw [← pow_succ, show n-1+1=n by omega]
    rw [hn']
    calc
      _ = (ks n hn 0 ^ (n-1) * (ks n hn 0 ^ (n-1))⁻¹) *
          (ks n hn 0 * ∏ i ∈ range (n-1), ks n hn (i+1)) := by ac_rfl
      _ = 1 := by rw [mul_inv_cancel, one_mul, hp]
  have hmid : (∏ i : Fin (n-2), (fun i : Fin (n-2) => kt n hn (i.val+1)) i) = ∏ i ∈ range (n-2), kt n hn (i+1) := by
    exact Fin.prod_univ_eq_prod_range (fun i => kt n hn (i+1)) (n-2)
  rw [show n-1=(n-2)+1 by omega, Finset.prod_range_succ] at hall
  rw [show n-2+1=n-1 by omega, ← hmid, ← mul_assoc] at hall
  have hinv : (kt n hn (n-1))⁻¹ = kt n hn (n-1) :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using kt_square n hn (n-1))
  exact hinv.symm.trans (eq_inv_of_mul_eq_one_left hall).symm

private theorem kernelHom_u (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : 1 ≤ k) (hk' : k < n) :
    kernelHom n hn (u n k) = kt n hn k := by
  by_cases h : k ≤ n-2
  · rw [u, dif_pos ⟨hk, h⟩, kernelHom_t]
    change kt n hn (k-1+1) = kt n hn k
    rw [show k-1+1=k by omega]
  · have hl : k = n-1 := by omega
    subst k
    rw [u_last n hn, map_mul, map_pow, kernelHom_s, ts, map_prod]
    simpa only [kernelHom_t] using (kt_last n hn).symm

private theorem kernelHom_e (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k < n) :
    kernelHom n hn (e n k) = ks n hn k := by
  by_cases h0 : k = 0
  · subst k; rw [e_zero n hn, kernelHom_s]; rfl
  rw [e, map_mul, kernelHom_s, kernelHom_u n hn k (by omega) hk, kt]
  simp [mul_left_comm]

private def backL (n : ℕ) (hn : 2 ≤ n) : L n →* G n := ((Subgroup.closure (kgens n))).subtype.comp (kernelHom n hn)
@[simp] private theorem backL_s (n : ℕ) (hn : 2 ≤ n) : backL n hn (s n) = (PresentedGroup.of (rels := rels n) 1) * ((PresentedGroup.of (rels := rels n) 0))⁻¹ := by
  simp only [backL, MonoidHom.comp_apply, kernelHom_s, Subgroup.subtype_apply, ks_coe]
  group
@[simp] private theorem backL_e (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k < n) :
    backL n hn (e n k) = (PresentedGroup.of (rels := rels n) 0) ^ (k : ℤ) * (PresentedGroup.of (rels := rels n) 1) * (PresentedGroup.of (rels := rels n) 0) ^ (-((k : ℤ)+1)) := by
  simp only [backL, MonoidHom.comp_apply, kernelHom_e n hn k hk, Subgroup.subtype_apply, ks_coe]

@[simp] private theorem backL_t (n : ℕ) (hn : 2 ≤ n) (i : Fin (n-2)) :
    backL n hn (t n i) = (ks n hn (i.val+1) : G n) * (ks n hn 0 : G n)⁻¹ := by
  simp only [backL, MonoidHom.comp_apply, kernelHom_t, kt, Subgroup.subtype_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, Nat.cast_add, Nat.cast_one]

@[simp] private theorem backR_cg (n : ℕ) : (cyclicHom n (PresentedGroup.of (rels := rels n) 0) (x_order n)) ((ofAdd (1 : ZMod n))) = (PresentedGroup.of (rels := rels n) 0) := by exact cyclicHom_one ..

private theorem back_generator (n : ℕ) (hn : 2 ≤ n) :
    (backL n hn).comp (stepAut n hn).toMonoidHom =
      (MulAut.conj ((PresentedGroup.of (rels := rels n) 0))).toMonoidHom.comp (backL n hn) := by
  apply L_hom_ext
  · change backL n hn (step n (s n)) = (PresentedGroup.of (rels := rels n) 0) * backL n hn (s n) * ((PresentedGroup.of (rels := rels n) 0))⁻¹
    rw [step_s, backL_e n hn 1 (by omega), backL_s]
    group
  · intro i
    change backL n hn (step n (t n i)) = (PresentedGroup.of (rels := rels n) 0) * backL n hn (t n i) * ((PresentedGroup.of (rels := rels n) 0))⁻¹
    rw [step_t, map_mul, map_inv, backL_e n hn (i.val+2) (by omega),
      backL_e n hn 1 (by omega), backL_t, ks_coe, ks_coe]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    group

private theorem back_compat (n : ℕ) (hn : 2 ≤ n) (g : Multiplicative (ZMod n)) :
    (backL n hn).comp (alpha n g).toMonoidHom =
      (MulAut.conj ((cyclicHom n (PresentedGroup.of (rels := rels n) 0) (x_order n)) g)).toMonoidHom.comp (backL n hn) := by
  have hgen (a : L n) : backL n hn (alpha n ((ofAdd (1 : ZMod n))) a) =
      (PresentedGroup.of (rels := rels n) 0) * backL n hn a * ((PresentedGroup.of (rels := rels n) 0))⁻¹ := by
    rw [alpha_generator n hn]
    exact DFunLike.congr_fun (back_generator n hn) a
  have hpow (k : ℕ) (a : L n) : backL n hn (alpha n ((ofAdd (1 : ZMod n)) ^ k) a) =
      (cyclicHom n (PresentedGroup.of (rels := rels n) 0) (x_order n)) ((ofAdd (1 : ZMod n)) ^ k) * backL n hn a * ((cyclicHom n (PresentedGroup.of (rels := rels n) 0) (x_order n)) ((ofAdd (1 : ZMod n)) ^ k))⁻¹ := by
    induction k generalizing a with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', map_mul, MulAut.mul_apply, hgen, ih]
      simp only [map_mul, backR_cg, mul_inv_rev]
      group
  letI : NeZero n := ⟨by omega⟩
  have hg : (ofAdd (1 : ZMod n)) ^ g.toAdd.val = g := by
    change ofAdd (g.toAdd.val • (1 : ZMod n)) = g
    simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rfl
  apply DFunLike.ext
  intro a
  change backL n hn (alpha n g a) = (cyclicHom n (PresentedGroup.of (rels := rels n) 0) (x_order n)) g * backL n hn a * ((cyclicHom n (PresentedGroup.of (rels := rels n) 0) (x_order n)) g)⁻¹
  simpa only [hg] using hpow g.toAdd.val a

private noncomputable def backward (n : ℕ) (hn : 2 ≤ n) : (L n ⋊[alpha n] Multiplicative (ZMod n)) →* G n :=
  SemidirectProduct.lift (backL n hn) ((cyclicHom n (PresentedGroup.of (rels := rels n) 0) (x_order n))) (back_compat n hn)


private theorem backL_square (n : ℕ) (hn : 2 ≤ n) : backL n hn (s n ^ 2) = (PresentedGroup.of (rels := rels n) 2) := by
  rw [backL, MonoidHom.comp_apply, map_pow, kernelHom_s]
  exact ks_square_z n hn 0

private theorem backward_forward (n : ℕ) (hn : 2 ≤ n) :
    (backward n hn).comp (forward n hn) = MonoidHom.id (G n) := by
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · simp [forward_of, fg, backward]
  · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, forward_of]
    change backward n hn (v n) = (PresentedGroup.of (rels := rels n) 1)
    simp [backward, v, mul_assoc]
  · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, forward_of]
    change backward n hn ((SemidirectProduct.inl (s n ^ 2) : L n ⋊[alpha n] Multiplicative (ZMod n))) = (PresentedGroup.of (rels := rels n) 2)
    simp only [backward, SemidirectProduct.lift_inl, backL_square]

private theorem ks_succ_coe (n : ℕ) (hn : 2 ≤ n) (i : ℤ) :
    (ks n hn (i+1) : G n) = (PresentedGroup.of (rels := rels n) 0) * (ks n hn i : G n) * ((PresentedGroup.of (rels := rels n) 0))⁻¹ := by
  rw [ks_coe, ks_coe]
  group

private theorem forward_ks (n : ℕ) (hn : 2 ≤ n) (i : ℕ) (hi : i ≤ n) :
    forward n hn (ks n hn i : G n) = SemidirectProduct.inl (e n i) := by
  induction i with
  | zero =>
    simp only [Nat.cast_zero]
    have hbase : (ks n hn 0 : G n) = (PresentedGroup.of (rels := rels n) 1) * ((PresentedGroup.of (rels := rels n) 0))⁻¹ := by rw [ks_coe]; group
    rw [hbase, e_zero n hn]
    simp [fg, v]
  | succ i ih =>
    have hsucc : (ks n hn (i+1 : ℕ) : G n) = (PresentedGroup.of (rels := rels n) 0) * (ks n hn i : G n) * ((PresentedGroup.of (rels := rels n) 0))⁻¹ := by
      simpa only [Nat.cast_add, Nat.cast_one] using ks_succ_coe n hn i
    rw [hsucc, map_mul, map_mul, map_inv, ih (by omega)]
    have hx : forward n hn ((PresentedGroup.of (rels := rels n) 0)) = (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) := by simp [fg]
    rw [hx]
    calc
      _ = SemidirectProduct.inl (alpha n ((ofAdd (1 : ZMod n))) (e n i)) := by
        simpa only [map_inv] using
          (SemidirectProduct.inl_aut (φ := alpha n) ((ofAdd (1 : ZMod n))) (e n i)).symm
      _ = _ := by
        congr 1
        rw [alpha_generator n hn]
        exact step_e n hn i (by omega)

private theorem forward_backward (n : ℕ) (hn : 2 ≤ n) :
    (forward n hn).comp (backward n hn) = MonoidHom.id ((L n ⋊[alpha n] Multiplicative (ZMod n))) := by
  apply SemidirectProduct.hom_ext
  · apply L_hom_ext
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, backward,
        SemidirectProduct.lift_inl]
      rw [backL_s, map_mul, map_inv]
      have hx : forward n hn ((PresentedGroup.of (rels := rels n) 0)) = (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n)) := by simp [fg]
      have hy : forward n hn ((PresentedGroup.of (rels := rels n) 1)) = v n := by simp [fg]
      rw [hx, hy, v]; group
    · intro i
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, backward,
        SemidirectProduct.lift_inl, backL_t, map_mul, map_inv]
      have hki : forward n hn (ks n hn ((i.val : ℤ)+1) : G n) =
          SemidirectProduct.inl (e n (i.val+1)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using forward_ks n hn (i.val+1) (by omega)
      have hf0 : forward n hn (ks n hn 0 : G n) = SemidirectProduct.inl (s n) := by
        simpa only [Nat.cast_zero, e_zero n hn] using forward_ks n hn 0 (by omega)
      rw [hki, hf0]
      rw [e, u_basis, ← map_inv, ← map_mul]
      congr 1
      simp
  · apply cyclicHom_ext
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, backward,
      SemidirectProduct.lift_inr]
    change forward n hn ((cyclicHom n (PresentedGroup.of (rels := rels n) 0) (x_order n)) ((ofAdd (1 : ZMod n)))) = (SemidirectProduct.inr (ofAdd (1 : ZMod n)) : L n ⋊[alpha n] Multiplicative (ZMod n))
    rw [backR_cg]
    simp [fg]

theorem result : claim := fun n hn =>
  ⟨(forward n hn).toMulEquiv (backward n hn)
    (backward_forward n hn) (forward_backward n hn)⟩


end
end D5.S3.Quantum.Algebra.GeneralizedCHSHGroupDecomposition
