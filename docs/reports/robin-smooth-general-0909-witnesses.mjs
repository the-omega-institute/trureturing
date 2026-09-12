// Specified numerical witnesses, not a search over smooth integers.
const gamma = 0.5772156649015329;
const expGamma = Math.exp(gamma);
function witness(name, primes, factors) {
  const n = factors.reduce((v, [p, a]) => v * BigInt(p) ** BigInt(a), 1n);
  const sigma = factors.reduce((v, [p, a]) =>
    v * ((BigInt(p) ** BigInt(a + 1) - 1n) / BigInt(p - 1)), 1n);
  const N = Number(n);
  const C = primes.reduce((v, p) => v * p / (p - 1), 1);
  const logN = Math.log(N);
  const loglog = N === 1 ? 0 : Math.log(logN);
  const lhs = Number(sigma) / N;
  const rhs = expGamma * loglog;
  return {
    name, P: primes, factors, n: String(n), sigma: String(sigma),
    smooth: factors.every(([p, a]) => a === 0 || primes.includes(p)),
    unused_primes: primes.filter(p => n % BigInt(p) !== 0n),
    n_positive: n > 0n, n_gt_e: N > Math.E, C,
    threshold_lhs: C / expGamma, threshold_rhs: loglog,
    threshold_holds: C / expGamma < loglog,
    T: Math.exp(Math.exp(C / expGamma)),
    robin_lhs: lhs, robin_rhs: rhs, robin_holds: lhs < rhs,
    log_convention: N === 1 ? 'Lean Real.log 0 = 0; not a real analytic log at 0' : 'ordinary positive arguments'
  };
}
const witnesses = [
  witness('positive_with_unused_prime', [2, 3], [[2, 10]]),
  witness('positive_seven_smooth_tail', [2, 3, 5, 7], [[2, 18]]),
  witness('negative_threshold_only', [2, 3, 5, 7], [[2, 4], [3, 2], [5, 1], [7, 1]]),
  witness('degenerate_one_empty', [], []),
  witness('degenerate_two_below_e', [2], [[2, 1]])
];
if (!witnesses[0].threshold_holds || !witnesses[0].robin_holds ||
    !witnesses[1].threshold_holds || !witnesses[1].robin_holds ||
    witnesses[2].threshold_holds || witnesses[2].robin_holds || !witnesses[2].n_gt_e) {
  throw new Error('Witness expectations failed');
}
console.log(JSON.stringify({
  arithmetic: 'exact BigInt n and sigma via prime-power formulas; IEEE-754 transcendental diagnostics',
  gamma, expGamma, witnesses
}, null, 2));
