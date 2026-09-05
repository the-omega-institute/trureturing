#!/usr/bin/env python3
"""Generate the 61-mode golden germ jet certificate.

Usage:
  germ_jet_certificate.py --modes 0-60 --output D5/S3/Analytic/GermWindow/GermZeroCertificate.lean --metadata /tmp/germ-jet.json
  germ_jet_certificate.py --modes 0-60 --output D5/S3/Analytic/GermWindow/GermZeroCertificate.lean --metadata /tmp/germ-jet.json --check
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import tempfile
from fractions import Fraction as F
from pathlib import Path


C_RE = F(23815329946211908, 10**17)
C_IM = F(5256712292901926, 10**15)
PI_APPROX = F(314159265358979323846, 10**20)
PI_ERROR = F(1, 10**19)
PHI_LO = F(8090169943749474241, 5 * 10**18)
PHI_HI = F(161803398874989484821, 10**20)
LOG_ORDER = 70
LOG_APPROX = sum(F(1, 2) ** (i + 1) / (i + 1) for i in range(LOG_ORDER))
LOG_ERROR = F(1, 2**LOG_ORDER)
LOG_LO = LOG_APPROX - LOG_ERROR
LOG_HI = LOG_APPROX + LOG_ERROR
INTERVAL_DEN = 10**18
TAYLOR_DEN = 10**20
EXP_ORDER = 20
TRIG_ORDER = 10
BOUND_DEN = 10**18
FLOORS = [
    1, 3, 4, 6, 8, 9, 11, 12, 14, 16, 17, 19, 21, 22, 24, 25,
    27, 29, 30, 32, 33, 35, 37, 38, 40, 42, 43, 45, 46, 48, 50,
    51, 53, 55, 56, 58, 59, 61, 63, 64, 66, 67, 69, 71, 72, 74,
    76, 77, 79, 80, 82, 84, 85, 87, 88, 90, 92, 93, 95, 97, 98,
]


def floor_to(value: F, denominator: int) -> F:
    return F(value.numerator * denominator // value.denominator, denominator)


def ceil_to(value: F, denominator: int) -> F:
    return -floor_to(-value, denominator)


def nearest_to(value: F, denominator: int) -> F:
    lower = floor_to(value, denominator)
    upper = lower + F(1, denominator)
    return lower if value - lower <= upper - value else upper


def lean_q(value: F) -> str:
    if value.denominator == 1:
        return f"({value.numerator})"
    return f"({value.numerator} / {value.denominator})"


def lean_r(value: F) -> str:
    if value.denominator == 1:
        return f"(({value.numerator} : ℚ) : ℝ)"
    return f"(({value.numerator} / {value.denominator} : ℚ) : ℝ)"


def fraction_text(value: F) -> str:
    return f"{value.numerator}/{value.denominator}"


def taylor_exp(value: F, order: int) -> F:
    return sum(value**i / math.factorial(i) for i in range(order))


def taylor_cos(value: F, order: int) -> F:
    return sum(F((-1) ** i) * value ** (2 * i) / math.factorial(2 * i)
               for i in range(order))


def taylor_sin(value: F, order: int) -> F:
    return sum(F((-1) ** i) * value ** (2 * i + 1) /
               math.factorial(2 * i + 1) for i in range(order))


class Mode:
    def __init__(self, v: int) -> None:
        self.v = v
        floor = FLOORS[v]
        self.beta_lo = F(floor - 1 - v) + v * PHI_LO
        self.beta_hi = F(floor - 1 - v) + v * PHI_HI
        self.x_lo = floor_to(C_RE * self.beta_lo * LOG_LO, INTERVAL_DEN)
        self.x_hi = ceil_to(C_RE * self.beta_hi * LOG_HI, INTERVAL_DEN)
        self.theta_lo = floor_to(C_IM * self.beta_lo * LOG_LO, INTERVAL_DEN)
        self.theta_hi = ceil_to(C_IM * self.beta_hi * LOG_HI, INTERVAL_DEN)
        self.amp_lo = floor_to(self.beta_lo * LOG_LO, INTERVAL_DEN)
        self.amp_hi = ceil_to(self.beta_hi * LOG_HI, INTERVAL_DEN)
        theta_mid = (self.theta_lo + self.theta_hi) / 2
        self.quadrant = round(float(theta_mid) / (math.pi / 2))
        self.swap = self.quadrant % 2 == 1
        self.phase_index = self.quadrant // 2
        if self.swap:
            self.phase_lo = self.theta_lo - PI_APPROX / 2 - PI_ERROR / 2
            self.phase_hi = self.theta_hi - PI_APPROX / 2 + PI_ERROR / 2
        else:
            self.phase_lo = self.theta_lo
            self.phase_hi = self.theta_hi
        phase_mid = (self.phase_lo + self.phase_hi) / 2
        self.r0 = phase_mid - self.phase_index * PI_APPROX
        self.pi_err = abs(self.phase_index) * PI_ERROR
        self.r_delta = (self.phase_hi - self.phase_lo) / 2 + self.pi_err

        cos_poly = taylor_cos(self.r0, TRIG_ORDER)
        sin_poly = taylor_sin(self.r0, TRIG_ORDER)
        self.cos0 = nearest_to(cos_poly, TAYLOR_DEN)
        self.sin0 = nearest_to(sin_poly, TAYLOR_DEN)
        cos_round = abs(cos_poly - self.cos0)
        sin_round = abs(sin_poly - self.sin0)
        cos_rem = abs(self.r0) ** (2 * TRIG_ORDER) / math.factorial(2 * TRIG_ORDER)
        sin_rem = abs(self.r0) ** (2 * TRIG_ORDER + 1) / math.factorial(2 * TRIG_ORDER + 1)
        self.cos_base_err = cos_rem + cos_round
        self.sin_base_err = sin_rem + sin_round
        self.cos_err = ceil_to(self.r_delta + self.cos_base_err, TAYLOR_DEN)
        self.sin_err = ceil_to(self.r_delta + self.sin_base_err, TAYLOR_DEN)

        self.scale = max(1, math.ceil(float(self.x_hi)))
        self.q_lo = -self.x_hi / self.scale
        self.q_hi = -self.x_lo / self.scale
        exp_poly_lo = taylor_exp(self.q_lo, EXP_ORDER)
        exp_poly_hi = taylor_exp(self.q_hi, EXP_ORDER)
        exp_rem_lo = (abs(self.q_lo) ** EXP_ORDER *
                      F(EXP_ORDER + 1, math.factorial(EXP_ORDER) * EXP_ORDER))
        exp_rem_hi = (abs(self.q_hi) ** EXP_ORDER *
                      F(EXP_ORDER + 1, math.factorial(EXP_ORDER) * EXP_ORDER))
        self.base_lo = floor_to(exp_poly_lo - exp_rem_lo, TAYLOR_DEN)
        self.base_hi = ceil_to(exp_poly_hi + exp_rem_hi, TAYLOR_DEN)
        self.exp_lo = floor_to(self.base_lo**self.scale, TAYLOR_DEN)
        self.exp_hi = ceil_to(self.base_hi**self.scale, TAYLOR_DEN)
        self.exp0 = (self.exp_lo + self.exp_hi) / 2
        self.exp_err = (self.exp_hi - self.exp_lo) / 2

        sign = F((-1) ** self.phase_index)
        if self.swap:
            self.theta_cos0 = -sign * self.sin0
            self.theta_sin0 = sign * self.cos0
            self.theta_cos_err = self.sin_err
            self.theta_sin_err = self.cos_err
        else:
            self.theta_cos0 = sign * self.cos0
            self.theta_sin0 = sign * self.sin0
            self.theta_cos_err = self.cos_err
            self.theta_sin_err = self.sin_err

        self.term_re0 = self.exp0 * self.theta_cos0
        self.term_re_err = self.exp_err + abs(self.exp0) * self.theta_cos_err
        self.term_im0 = -self.exp0 * self.theta_sin0
        self.term_im_err = self.exp_err + abs(self.exp0) * self.theta_sin_err
        self.term_re_lo = floor_to(self.term_re0 - self.term_re_err, BOUND_DEN)
        self.term_re_hi = ceil_to(self.term_re0 + self.term_re_err, BOUND_DEN)
        self.term_im_lo = floor_to(self.term_im0 - self.term_im_err, BOUND_DEN)
        self.term_im_hi = ceil_to(self.term_im0 + self.term_im_err, BOUND_DEN)
        self.term_re_bound_err = max(self.term_re0 - self.term_re_lo,
                                     self.term_re_hi - self.term_re0)
        self.term_im_bound_err = max(self.term_im0 - self.term_im_lo,
                                     self.term_im_hi - self.term_im0)

        self.amp0 = (self.amp_lo + self.amp_hi) / 2
        self.amp_err = (self.amp_hi - self.amp_lo) / 2
        self.deriv_re0 = -self.amp0 * self.term_re0
        self.deriv_re_err = self.amp_err + abs(self.amp0) * self.term_re_bound_err
        self.deriv_im0 = -self.amp0 * self.term_im0
        self.deriv_im_err = self.amp_err + abs(self.amp0) * self.term_im_bound_err
        self.deriv_re_lo = floor_to(self.deriv_re0 - self.deriv_re_err, BOUND_DEN)
        self.deriv_re_hi = ceil_to(self.deriv_re0 + self.deriv_re_err, BOUND_DEN)
        self.deriv_im_lo = floor_to(self.deriv_im0 - self.deriv_im_err, BOUND_DEN)
        self.deriv_im_hi = ceil_to(self.deriv_im0 + self.deriv_im_err, BOUND_DEN)

    def metadata(self) -> dict[str, object]:
        return {
            "deriv_im_interval": [fraction_text(self.deriv_im_lo), fraction_text(self.deriv_im_hi)],
            "deriv_re_interval": [fraction_text(self.deriv_re_lo), fraction_text(self.deriv_re_hi)],
            "phase_index": self.phase_index,
            "quadrant": self.quadrant,
            "term_im_interval": [fraction_text(self.term_im_lo), fraction_text(self.term_im_hi)],
            "term_re_interval": [fraction_text(self.term_re_lo), fraction_text(self.term_re_hi)],
            "v": self.v,
        }


def term_expression(v: int) -> str:
    return f"(2 : ℂ) ^ (-c * (o5Beta {v} : ℂ))"


def deriv_expression(v: int) -> str:
    return f"-(o5Beta {v} : ℂ) * (Real.log 2 : ℂ) * {term_expression(v)}"


def coordinate_pair(expression: str, mode: Mode, prefix: str) -> str:
    re_lo = lean_r(getattr(mode, f"{prefix}_re_lo"))
    re_hi = lean_r(getattr(mode, f"{prefix}_re_hi"))
    im_lo = lean_r(getattr(mode, f"{prefix}_im_lo"))
    im_hi = lean_r(getattr(mode, f"{prefix}_im_hi"))
    return (f"(({re_lo} ≤ ({expression}).re ∧ ({expression}).re ≤ {re_hi}) ∧ "
            f"({im_lo} ≤ ({expression}).im ∧ ({expression}).im ≤ {im_hi}))")


def full_term_type(mode: Mode) -> str:
    pair = coordinate_pair(term_expression(mode.v), mode, "term")
    return (f"({pair} ∧ ((({lean_r(mode.term_re_hi)} - {lean_r(mode.term_re_lo)}) ≤ 1 / 10 ^ 15) ∧ "
            f"(({lean_r(mode.term_im_hi)} - {lean_r(mode.term_im_lo)}) ≤ 1 / 10 ^ 15)))")


def full_deriv_type(mode: Mode) -> str:
    pair = coordinate_pair(deriv_expression(mode.v), mode, "deriv")
    return (f"({pair} ∧ ((({lean_r(mode.deriv_re_hi)} - {lean_r(mode.deriv_re_lo)}) ≤ 1 / 10 ^ 15) ∧ "
            f"(({lean_r(mode.deriv_im_hi)} - {lean_r(mode.deriv_im_lo)}) ≤ 1 / 10 ^ 15)))")


def term_arguments(mode: Mode) -> str:
    values = [
        mode.beta_lo, mode.beta_hi, mode.x_lo, mode.x_hi, mode.theta_lo,
        mode.theta_hi, mode.phase_lo, mode.phase_hi, mode.r0, mode.r_delta,
        mode.pi_err, mode.q_lo, mode.q_hi, mode.base_lo, mode.base_hi,
        mode.exp_lo, mode.exp_hi, mode.exp0, mode.exp_err, mode.cos0,
        mode.sin0, mode.cos_base_err, mode.sin_base_err, mode.cos_err,
        mode.sin_err, mode.theta_cos0, mode.theta_sin0, mode.theta_cos_err,
        mode.theta_sin_err, mode.term_re_lo, mode.term_re_hi,
        mode.term_im_lo, mode.term_im_hi,
    ]
    return " ".join(lean_q(value) for value in values)


def deriv_arguments(mode: Mode) -> str:
    values = [
        mode.beta_lo, mode.beta_hi, mode.exp0, mode.theta_cos0,
        mode.theta_sin0, mode.term_re_bound_err, mode.term_im_bound_err,
        mode.term_re_lo, mode.term_re_hi, mode.term_im_lo, mode.term_im_hi,
        mode.amp0, mode.amp_err, mode.deriv_re_lo, mode.deriv_re_hi,
        mode.deriv_im_lo, mode.deriv_im_hi,
    ]
    return " ".join(lean_q(value) for value in values)


NORM_NUM = "norm_num [c, o5FloorTable, phaseIndexPi, piApprox, Finset.sum_range_succ, Nat.factorial]"


def mode_source(mode: Mode) -> str:
    pair = f"({coordinate_pair(term_expression(mode.v), mode, 'term')} ∧ {coordinate_pair(deriv_expression(mode.v), mode, 'deriv')})"
    swap = "true" if mode.swap else "false"
    return "\n".join([
        f"private theorem mode_{mode.v}_enclosures : {pair} := by",
        f"  have ht : {full_term_type(mode)} := by",
        f"    apply mode_term_enclosure {mode.v} (by norm_num) {mode.scale} {swap} {term_arguments(mode)}",
        f"    all_goals {NORM_NUM}",
        f"  have hd : {full_deriv_type(mode)} := by",
        f"    apply mode_deriv_enclosure {mode.v} (by norm_num) {deriv_arguments(mode)} (hterm := ht)",
        f"    all_goals {NORM_NUM}",
        "  exact ⟨ht.1, hd.1⟩",
    ])


HEADER = """/- GID: D5/S3/Analytic/GermWindow/GermZeroCertificate
   generality: I
   mirror-B: D5/B/S3/Analytic/GermWindow/GermZeroCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Generated 61-mode certificate for the golden germ candidate zero. -/

import D5.S3.Analytic.GermWindow.GermJetModeLemma
import D5.S3.Analytic.GermWindow.GermZeroCertificateReduction
import D5.S3.Analytic.GermWindow.GermZeroCertificateJet
import D5.S3.Analytic.Certified.TrigEnvelopePhaseReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex
open scoped BigOperators
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.GermWindow.GermJetModeLemma
open D5.S3.Analytic.GermWindow.GermZeroCertificateReduction
open D5.S3.Analytic.GermWindow.GermZeroCertificateJet
open D5.S3.Analytic.Certified.TrigEnvelopePhaseReduction

noncomputable section

namespace D5.S3.Analytic.GermWindow.GermZeroCertificate

"""


def bounds_source(modes: list[Mode]) -> str:
    rows = "\n".join(
        f"  | {m.v} => ⟨{lean_q(m.term_re_lo)}, {lean_q(m.term_re_hi)}, {lean_q(m.term_im_lo)}, {lean_q(m.term_im_hi)}, {lean_q(m.deriv_re_lo)}, {lean_q(m.deriv_re_hi)}, {lean_q(m.deriv_im_lo)}, {lean_q(m.deriv_im_hi)}⟩"
        for m in modes
    )
    return f"""private structure ModeBounds where
  termReLo : ℚ
  termReHi : ℚ
  termImLo : ℚ
  termImHi : ℚ
  derivReLo : ℚ
  derivReHi : ℚ
  derivImLo : ℚ
  derivImHi : ℚ

private def modeBounds : ℕ → ModeBounds
{rows}
  | _ => ⟨0, 0, 0, 0, 0, 0, 0, 0⟩
"""


def assembly_source(modes: list[Mode]) -> str:
    term_re_lo_sum = sum(m.term_re_lo for m in modes)
    term_re_hi_sum = sum(m.term_re_hi for m in modes)
    term_im_lo_sum = sum(m.term_im_lo for m in modes)
    term_im_hi_sum = sum(m.term_im_hi for m in modes)
    deriv_re_lo_sum = sum(m.deriv_re_lo for m in modes)
    re_abs = max(-term_re_lo_sum, term_re_hi_sum)
    im_abs = max(-term_im_lo_sum, term_im_hi_sum)
    dispatcher = "\n".join(
        f"  · simpa only [modeBounds] using mode_{m.v}_enclosures" for m in modes
    )
    return f"""
private theorem all_mode_enclosures (v : ℕ) (hv : v < 61) :
    (((((modeBounds v).termReLo : ℝ) ≤ ({term_expression('v')}).re ∧ ({term_expression('v')}).re ≤ (modeBounds v).termReHi) ∧ (((modeBounds v).termImLo : ℝ) ≤ ({term_expression('v')}).im ∧ ({term_expression('v')}).im ≤ (modeBounds v).termImHi)) ∧
      ((((modeBounds v).derivReLo : ℝ) ≤ ({deriv_expression('v')}).re ∧ ({deriv_expression('v')}).re ≤ (modeBounds v).derivReHi) ∧ (((modeBounds v).derivImLo : ℝ) ≤ ({deriv_expression('v')}).im ∧ ({deriv_expression('v')}).im ≤ (modeBounds v).derivImHi))) := by
  interval_cases v
{dispatcher}

private theorem generated_term_sum_re_bounds :
    (∑ v ∈ Finset.range 61, ((modeBounds v).termReLo : ℝ)) ≤ (∑ v ∈ Finset.range 61, {term_expression('v')}).re ∧
      (∑ v ∈ Finset.range 61, {term_expression('v')}).re ≤ ∑ v ∈ Finset.range 61, ((modeBounds v).termReHi : ℝ) := by
  apply sum_re_le_of_bounds
  intro v hv
  exact (all_mode_enclosures v (by simpa using hv)).1.1

private theorem generated_term_sum_im_bounds :
    (∑ v ∈ Finset.range 61, ((modeBounds v).termImLo : ℝ)) ≤ (∑ v ∈ Finset.range 61, {term_expression('v')}).im ∧
      (∑ v ∈ Finset.range 61, {term_expression('v')}).im ≤ ∑ v ∈ Finset.range 61, ((modeBounds v).termImHi : ℝ) := by
  apply sum_im_le_of_bounds
  intro v hv
  exact (all_mode_enclosures v (by simpa using hv)).1.2

private theorem generated_deriv_sum_re_bounds :
    (∑ v ∈ Finset.range 61, ((modeBounds v).derivReLo : ℝ)) ≤ (∑ v ∈ Finset.range 61, {deriv_expression('v')}).re ∧
      (∑ v ∈ Finset.range 61, {deriv_expression('v')}).re ≤ ∑ v ∈ Finset.range 61, ((modeBounds v).derivReHi : ℝ) := by
  apply sum_re_le_of_bounds
  intro v hv
  exact (all_mode_enclosures v (by simpa using hv)).2.1

set_option maxHeartbeats 1000000 in
-- Exact normalization expands all 61 generated lower endpoints.
private theorem center_re_lower : {lean_r(term_re_lo_sum)} ≤ (∑ v ∈ Finset.range 61, {term_expression('v')}).re := by
  calc
    {lean_r(term_re_lo_sum)} = ∑ v ∈ Finset.range 61, ((modeBounds v).termReLo : ℝ) := by norm_num [modeBounds, Finset.sum_range_succ]
    _ ≤ _ := generated_term_sum_re_bounds.1

set_option maxHeartbeats 1000000 in
-- Exact normalization expands all 61 generated upper endpoints.
private theorem center_re_upper : (∑ v ∈ Finset.range 61, {term_expression('v')}).re ≤ {lean_r(term_re_hi_sum)} := by
  calc
    _ ≤ ∑ v ∈ Finset.range 61, ((modeBounds v).termReHi : ℝ) := generated_term_sum_re_bounds.2
    _ = {lean_r(term_re_hi_sum)} := by norm_num [modeBounds, Finset.sum_range_succ]

set_option maxHeartbeats 1000000 in
-- Exact normalization expands all 61 generated lower endpoints.
private theorem center_im_lower : {lean_r(term_im_lo_sum)} ≤ (∑ v ∈ Finset.range 61, {term_expression('v')}).im := by
  calc
    {lean_r(term_im_lo_sum)} = ∑ v ∈ Finset.range 61, ((modeBounds v).termImLo : ℝ) := by norm_num [modeBounds, Finset.sum_range_succ]
    _ ≤ _ := generated_term_sum_im_bounds.1

set_option maxHeartbeats 1000000 in
-- Exact normalization expands all 61 generated upper endpoints.
private theorem center_im_upper : (∑ v ∈ Finset.range 61, {term_expression('v')}).im ≤ {lean_r(term_im_hi_sum)} := by
  calc
    _ ≤ ∑ v ∈ Finset.range 61, ((modeBounds v).termImHi : ℝ) := generated_term_sum_im_bounds.2
    _ = {lean_r(term_im_hi_sum)} := by norm_num [modeBounds, Finset.sum_range_succ]

private theorem local_term_hasDerivAt (s : ℂ) (v : ℕ) :
    HasDerivAt (fun z : ℂ => (2 : ℂ) ^ (-z * (o5Beta v : ℂ)))
      ((2 : ℂ) ^ (-s * (o5Beta v : ℂ)) * Complex.log 2 * (-(o5Beta v : ℂ))) s := by
  have he : HasDerivAt (fun z : ℂ => -z * (o5Beta v : ℂ))
      (-(o5Beta v : ℂ)) s := by
    simpa [id] using (hasDerivAt_id s).neg.mul_const (o5Beta v : ℂ)
  simpa only [mul_assoc] using he.const_cpow (c := (2 : ℂ))
    (Or.inl (by norm_num))

private theorem deriv_g_eq_sum : deriv (g 60) c = ∑ v ∈ Finset.range 61, {deriv_expression('v')} := by
  unfold g
  calc
    deriv (fun s => ∑ v ∈ Finset.range 61, {term_expression('v').replace('-c', '-s')}) c =
        ∑ v ∈ Finset.range 61, {term_expression('v')} * Complex.log 2 * (-(o5Beta v : ℂ)) :=
      (HasDerivAt.fun_sum fun v _ => local_term_hasDerivAt c v).deriv
    _ = ∑ v ∈ Finset.range 61, {deriv_expression('v')} := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [show Complex.log (2 : ℂ) = (Real.log 2 : ℂ) from (Complex.ofReal_log (by norm_num)).symm]
      ring

/-- The generated coordinate assembly certifies the center norm. -/
theorem g60_center_norm_lt : ‖g 60 c‖ < 4 / 10 ^ 10 := by
  change ‖∑ v ∈ Finset.range 61, {term_expression('v')}‖ < 4 / 10 ^ 10
  have hre : |(∑ v ∈ Finset.range 61, {term_expression('v')}).re| ≤ {lean_r(re_abs)} := by
    rw [abs_le]
    constructor <;> linarith [center_re_lower, center_re_upper]
  have him : |(∑ v ∈ Finset.range 61, {term_expression('v')}).im| ≤ {lean_r(im_abs)} := by
    rw [abs_le]
    constructor <;> linarith [center_im_lower, center_im_upper]
  exact (norm_le_of_re_im_bounds hre him).trans_lt (by norm_num)

set_option maxHeartbeats 1000000 in
-- Exact normalization expands all 61 generated derivative lower endpoints.
/-- The 61-entry exact derivative sum exceeds the advertised `1.87` margin. -/
theorem g60_center_deriv_re_gt : 187 / 100 < (deriv (g 60) c).re := by
  rw [deriv_g_eq_sum]
  calc
    (187 / 100 : ℝ) < {lean_r(deriv_re_lo_sum)} := by norm_num
    _ = ∑ v ∈ Finset.range 61, ((modeBounds v).derivReLo : ℝ) := by norm_num [modeBounds, Finset.sum_range_succ]
    _ ≤ _ := generated_deriv_sum_re_bounds.1

/-- Bind-only closure: the `p = 2` golden local factor has a zero near `c`. -/
theorem germLocalFactor_two_has_zero_near_candidate :
    ∃ z ∈ Metric.ball c (1 / 10 ^ 8), germLocalFactor z 2 = 0 :=
  germ_zero_of_center_jet g60_center_norm_lt g60_center_deriv_re_gt g60_curvature_le

#print axioms g60_center_norm_lt
#print axioms g60_center_deriv_re_gt
#print axioms germLocalFactor_two_has_zero_near_candidate

end D5.S3.Analytic.GermWindow.GermZeroCertificate
"""


def render(modes: list[int]) -> tuple[str, str]:
    if modes != list(range(61)):
        raise ValueError("--modes must be exactly 0-60")
    data = [Mode(v) for v in modes]
    source = HEADER
    source += "\n".join(mode_source(mode) for mode in data)
    source += "\n\n" + bounds_source(data)
    source += assembly_source(data)
    metadata = {
        "certified_derivative_real_lower": fraction_text(sum(m.deriv_re_lo for m in data)),
        "certified_norm_l1_bound": fraction_text(
            max(-sum(m.term_re_lo for m in data), sum(m.term_re_hi for m in data)) +
            max(-sum(m.term_im_lo for m in data), sum(m.term_im_hi for m in data))),
        "exp_order": EXP_ORDER,
        "log_order": LOG_ORDER,
        "modes": modes,
        "per_mode": [mode.metadata() for mode in data],
        "trig_order": TRIG_ORDER,
    }
    return source, json.dumps(metadata, indent=2, sort_keys=True) + "\n"


def parse_modes(specification: str) -> list[int]:
    if specification == "0-60":
        return list(range(61))
    raise ValueError("--modes must be exactly 0-60")


def atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(content)
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--modes", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--metadata", required=True, type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        source, metadata = render(parse_modes(args.modes))
    except ValueError as error:
        parser.error(str(error))
    if args.check:
        with tempfile.TemporaryDirectory(prefix="germ-jet-certificate-check-") as directory:
            regenerated = Path(directory) / args.output.name
            regenerated.write_bytes(source.encode("utf-8"))
            if not args.output.is_file() or args.output.read_bytes() != regenerated.read_bytes():
                print(f"generated output differs: {args.output}", file=sys.stderr)
                return 1
        return 0
    atomic_write(args.output, source)
    atomic_write(args.metadata, metadata)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
