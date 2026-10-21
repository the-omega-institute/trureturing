using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualThreeNodeSymmetricDenominatorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual three-node SymmetricDenominator", H("Actual three-node SymmetricDenominator"),
        Blocks(
            Paragraph(Text("For either nonzero signed exterior node m, the actual nodal model and exact reciprocal evaluation give pi^2(1-(n/m)^2)^2 times the column norm square equal to the corresponding reciprocal numerator norm square divided by m^2.")),
            Paragraph(Text("The negative exterior node is proved to lie outside the literal head using the same radius |n|. After taking norm squares the positive and negative columns share a denominator, and their sum is precisely pairedTerm.")),
            Paragraph(Text("When N>0, |n|<N and m>N, the squared factors satisfy 0<(1-(n/N)^2)^2 <= (1-(n/m)^2)^2 <=1. These bounds depend on the nodes and cutoff, before any coefficient vector.")),
            Describe.Lean(DescribeId.Create("actual-single-symmetric-denominator"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeSymmetricDenominator.actual_single_symmetric_denominator"),
                H("actual single symmetric denominator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lemma actual_single_symmetric_denominator {n : ℤ} (hn : n ≠ 0) (c N : ℕ)\n    (hN : 0 < N) (v : ℤ → ℂ) (m : ℤ) (hm : m ≠ 0) (hmS : m ∉ threeNodes n) :\n    Real.pi ^ 2 * (1 - ((n : ℝ) / (m : ℝ)) ^ 2) ^ 2 *\n        ‖couplingColumn c (threeNodes n) v m‖ ^ 2 =\n      ‖value (reciprocalPolynomial 3 N (P c (threeNodes n) v)) ((N : ℝ) / m) -\n          (arithmeticBoundarySymbol c m : ℂ) *\n            value (reciprocalPolynomial 3 N (Q (threeNodes n) v)) ((N : ℝ) / m)‖ ^ 2 /\n        (m : ℝ) ^ 2"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("three-nodes-radius"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeSymmetricDenominator.threeNodes_radius"),
                H("threeNodes radius"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lemma threeNodes_radius (n : ℤ) :\n    ∀ k ∈ threeNodes n, |(k : ℝ)| ≤ |(n : ℝ)|"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-pair-symmetric-denominator"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeSymmetricDenominator.actual_pair_symmetric_denominator"),
                H("actual pair symmetric denominator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lemma actual_pair_symmetric_denominator {n : ℤ} (hn : n ≠ 0) (c N : ℕ)\n    (hN : 0 < N) (hR : |(n : ℝ)| < (N : ℝ)) (v : ℤ → ℂ) (j : ℕ) :\n    Real.pi ^ 2 * (1 - ((n : ℝ) / (N + j + 1 : ℕ)) ^ 2) ^ 2 *\n        pairedColumnTerm c N (threeNodes n) v j =\n      pairedTerm c N\n        (reciprocalPolynomial 3 N (P c (threeNodes n) v))\n        (reciprocalPolynomial 3 N (Q (threeNodes n) v)) j"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("symmetric-factor-bounds"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeSymmetricDenominator.symmetric_factor_bounds"),
                H("symmetric factor bounds"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lemma symmetric_factor_bounds {b N m : ℝ} (hN : 0 < N) (hR : |b| < N) (hNm : N < m) :\n    0 < (1 - (b / N) ^ 2) ^ 2 ∧\n      (1 - (b / N) ^ 2) ^ 2 ≤ (1 - (b / m) ^ 2) ^ 2 ∧\n      (1 - (b / m) ^ 2) ^ 2 ≤ 1"))), DescribeRole.Theorem))));
}
