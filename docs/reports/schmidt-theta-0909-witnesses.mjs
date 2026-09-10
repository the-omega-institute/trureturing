import assert from 'node:assert/strict';

// Independent finite diagnostic, not a Lean theorem or a numerical tolerance proof.
const occupation = [4, 2, 1, 1];
const sum = xs => xs.reduce((a, b) => a + b, 0);
const factorial = n => n < 2 ? 1 : n * factorial(n - 1);
const count = a => {
  assert.ok(a.every(n => Number.isInteger(n) && n >= 0));
  const denominator = a.reduce((p, n) => p * factorial(n), 1);
  assert.ok(denominator > 0);
  return factorial(sum(a)) / denominator;
};
const histogram = Array(22).fill(0);
const histories = [];

function enumerate(word, remaining, inversions) {
  if (sum(remaining) === 0) {
    histogram[inversions] += 1;
    histories.push(word);
    return;
  }
  for (let symbol = 0; symbol < remaining.length; symbol += 1) {
    if (remaining[symbol] === 0) continue;
    remaining[symbol] -= 1;
    enumerate([...word, symbol], remaining,
      inversions + word.filter(previous => previous > symbol).length);
    remaining[symbol] += 1;
  }
}

enumerate([], [...occupation], 0);
assert.equal(histories.length, 840);
assert.equal(count(occupation), histories.length);
const residues = Array(8).fill(0);
histogram.forEach((n, k) => { residues[k % 8] += n; });
const remainder = residues.slice(0, 4).map((n, k) => n - residues[k + 4]);
assert.deepEqual(remainder, [0, 0, 0, 0]);

const boundaries = Array.from({ length: 9 }, () => []);
for (let x = 0; x <= 4; x += 1)
  for (let y = 0; y <= 2; y += 1)
    for (let z = 0; z <= 1; z += 1)
      for (let w = 0; w <= 1; w += 1)
        boundaries[x + y + z + w].push([x, y, z, w]);

const cutProbabilities = boundaries.map(sectors => sectors.map(prefix => {
  const numerator = count(prefix) * count(occupation.map((n, k) => n - prefix[k]));
  assert.ok(numerator > 0 && histories.length > 0);
  return { prefix, numerator, denominator: histories.length };
}));
const entropies = cutProbabilities.map(sectors => {
  assert.equal(sum(sectors.map(p => p.numerator)), histories.length);
  return -sum(sectors.map(({ numerator, denominator }) => {
    const p = numerator / denominator;
    assert.ok(p > 0);
    return p * Math.log(p);
  }));
});
assert.deepEqual(boundaries.map(xs => xs.length), [1, 4, 8, 11, 12, 11, 8, 4, 1]);

// Rank is computed on the exact integer support matrix. A nonzero uniform
// normalization factor does not change it. The bad-length support is empty.
function supportMatrix(a) {
  return [0, 1].map(x => [0, 1].map(y =>
    Number(a[0] === Number(x === 0) + Number(y === 0) &&
      a[1] === Number(x === 1) + Number(y === 1))));
}
function rank2(m) {
  const determinant = m[0][0] * m[1][1] - m[0][1] * m[1][0];
  return determinant !== 0 ? 2 : m.flat().some(x => x !== 0) ? 1 : 0;
}
const validSupport = supportMatrix([1, 1]);
const invalidSupport = supportMatrix([1, 0]);
const validWordCount = sum(validSupport.flat());
const invalidWordCount = sum(invalidSupport.flat());
assert.equal(validWordCount, 2);
assert.equal(invalidWordCount, 0);
assert.equal(rank2(validSupport), 2);
assert.equal(rank2(invalidSupport), 0);
assert.equal([1, 0].filter(n => n > 0).length, 1);

// For the valid support, theta=pi changes one nonzero amplitude's sign.
// Both normalized Gram matrices are diag(1/2,1/2).
const phaseZeroSupport = validSupport;
const phasePiSupport = validSupport.map((row, x) =>
  row.map((entry, y) => x > y ? -entry : entry));
const gram = m => [0, 1].map(i => [0, 1].map(j =>
  sum([0, 1].map(k => m[k][i] * m[k][j])) / validWordCount));
assert.deepEqual(gram(phaseZeroSupport), [[0.5, 0], [0, 0.5]]);
assert.deepEqual(gram(phasePiSupport), [[0.5, 0], [0, 0.5]]);

// Dropping fixed occupation allows a global diagonal phase to change Schmidt
// coefficients: the four equal amplitudes have norm one at both phases.
const mixedZero = [[1, 1], [1, 1]];
const mixedPi = [[1, 1], [-1, 1]];
const mixedGram = m => [0, 1].map(i => [0, 1].map(j =>
  sum([0, 1].map(k => m[k][i] * m[k][j])) / 4));
assert.equal(sum(mixedZero.flat().map(x => x * x)), 4);
assert.equal(sum(mixedPi.flat().map(x => x * x)), 4);
assert.deepEqual(mixedGram(mixedZero), [[0.5, 0.5], [0.5, 0.5]]);
assert.deepEqual(mixedGram(mixedPi), [[0.5, 0], [0, 0.5]]);
assert.equal(rank2(mixedZero), 1);
assert.equal(rank2(mixedPi), 2);

function spectrum2(g) {
  assert.equal(g[0][1], g[1][0]);
  const trace = g[0][0] + g[1][1];
  const determinant = g[0][0] * g[1][1] - g[0][1] * g[1][0];
  const discriminant = trace * trace - 4 * determinant;
  assert.ok(g[0][0] >= 0 && g[1][1] >= 0 && determinant >= 0);
  assert.ok(discriminant >= 0);
  const root = Math.sqrt(discriminant);
  return [(trace + root) / 2, (trace - root) / 2];
}
const positiveSpectrum = spectrum2(gram(phaseZeroSupport));
assert.deepEqual(positiveSpectrum, spectrum2(gram(phasePiSupport)));
const mixedZeroSpectrum = spectrum2(mixedGram(mixedZero));
const mixedPiSpectrum = spectrum2(mixedGram(mixedPi));
assert.deepEqual(positiveSpectrum, [0.5, 0.5]);
assert.deepEqual(mixedZeroSpectrum, [1, 0]);
assert.deepEqual(mixedPiSpectrum, [0.5, 0.5]);

console.log(JSON.stringify({
  historyCount: histories.length,
  inversionHistogram: histogram,
  residuesModulo8: residues,
  exactRemainderModuloQ4Plus1: remainder,
  overlapAtPiOver4: { exact: '0/840 = 0', leanProof: false },
  rankSequence: boundaries.map(xs => xs.length),
  cut4: cutProbabilities[4],
  cutEntropiesNaturalLogApprox: entropies,
  nonemptyWitnesses: {
    positive: {
      occupation: [1, 1], cut: [1, 1], cardinalityPremise: '2 = 1 + 1',
      legalWords: validWordCount, squareRootArgument: validWordCount,
      schmidtSquaresAtZeroAndPi: positiveSpectrum,
      rank: rank2(validSupport), boundaryCount: 2,
      entropyApprox: Math.log(2)
    },
    negativeCardinality: {
      occupation: [1, 0], cut: [1, 1], cardinalityPremise: '1 != 1 + 1',
      legalWords: invalidWordCount, normalizationExists: false,
      totalizedCoefficientMatrixRank: rank2(invalidSupport), boundaryCount: 1,
      failedConclusion: '0 != 1'
    },
    negativeFixedOccupation: {
      amplitudesAtZero: [[0.5, 0.5], [0.5, 0.5]],
      amplitudesAtPi: [[0.5, 0.5], [-0.5, 0.5]],
      occupiedSectors: [[2, 0], [1, 1], [0, 2]],
      fixedOccupationPremise: false,
      normSquaredAtBothPhases: 1,
      schmidtSquaresAtZero: mixedZeroSpectrum, schmidtSquaresAtPi: mixedPiSpectrum,
      rankAtZero: rank2(mixedZero), rankAtPi: rank2(mixedPi),
      entropyAtZero: 0, entropyAtPiApprox: Math.log(2),
      failedConclusion: '[1,0] != [1/2,1/2]'
    }
  },
  nonclaims: [
    'The integer diagnostic is not a Lean proof of cross-theta orthogonality.',
    'Floating entropy decimals are approximations, not interval certificates.',
    'No division or logarithm is evaluated for the invalid-length witness.'
  ]
}, null, 2));
