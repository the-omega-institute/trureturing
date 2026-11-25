using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class HermiteHighestCoefficientDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Interpolation/HermiteHighestCoefficient";
    private const string Digest =
        "Sharp recovery of the quartic coefficient from two Hermite prefix differences.";
    private const string NewtonTail =
        "D5/S3/Analytic/Interpolation/ConfluentPositiveSampling.weightedNewtonTail";
    private const string MatrixTail =
        "D5/S3/Analytic/Interpolation/ConfluentHermiteObservation.matrixHermiteTail";
    private const string DeBoor = "D5/L/Estimation/deboor2005divideddifferences";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader(Module, Digest, "analytic-observation-bound-without-executable-mirror"),
        H("Sharp quartic coefficient recovery from Hermite data"),
        Blocks(
            Paragraph(Text("Let x, y, z be the three nodes, in observation order. Put "
                + "A = x² + xy + y², B = x³ + x²y + xy² + y³, C = x + y + z, "
                + "and D = A + (x + y)z + z². For data from the cubic and quartic "
                + "monomials the two rows are (A, B) and (C, D). Successive monic "
                + "division gives these formulas for repeated nodes as well.")),
            Describe.Lean(
                DescribeId.Create("inverse-two"), DeclarationHandle.Create(Module + ".inverseTwo"),
                H("Explicit two-coordinate inverse"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With determinant Δ = AD − BC and data (d₀, d₁), "
                    + "the inverse coefficients are (Dd₀ − Bd₁)/Δ and (Ad₁ − Cd₀)/Δ."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-newton-tail-two-inverse"),
                DeclarationHandle.Create(Module + ".weightedNewtonTail_two_inverse"),
                H("Two-sided inversion of the Newton data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(DeBoor)),
                Blocks(
                    Paragraph(Text("For every triple of positive nodes, the explicit map is "
                        + "both a left and a right inverse to "), Ref(NewtonTail),
                        Text(" with weight exponent 3 and two coefficient coordinates.")),
                    Paragraph(Text("The determinant equals x²y² + xyz(x + y) + z²A, "
                        + "which is positive even at complete coalescence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("highest-weight-zero"),
                DeclarationHandle.Create(Module + ".highestWeight0"),
                H("First weight"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quartic coefficient uses weight −C/Δ "
                    + "on the first positive-order difference."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("highest-weight-one"),
                DeclarationHandle.Create(Module + ".highestWeight1"),
                H("Second weight"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quartic coefficient uses weight A/Δ "
                    + "on the second positive-order difference."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("highest-row-sum"),
                DeclarationHandle.Create(Module + ".highestRowSum"),
                H("Absolute row sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute values of the two weights sum to "
                    + "(C + A)/Δ at positive nodes."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("highest-row-sum-optimal"),
                DeclarationHandle.Create(Module + ".highestRowSum_optimal"),
                H("Optimal nodes in the positive unit cube"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nodes in (0, 1], the absolute row sum is at least 1. "
                    + "Equality holds exactly when all three nodes are 1. The determinant "
                    + "is at most twice each of A and C, and equality in the bound by "
                    + "twice A forces all three nodes to be 1."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("highest-coefficient-worst-case"),
                DeclarationHandle.Create(Module + ".highestCoefficient_worst_case"),
                H("Exact scalar worst case"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over all scalar coefficient vectors whose two "
                    + "Newton observations have sup norm at most ε, for ε ≥ 0, the "
                    + "greatest absolute quartic coefficient is ε times the absolute row "
                    + "sum. The inverse of the data (−ε, ε) attains this value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("recover-highest"),
                DeclarationHandle.Create(Module + ".recoverHighest"),
                H("Matrix coefficient estimator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the two signed weights to the two "
                    + "real two-by-two Hermite blocks and add the resulting matrices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("matrix-hermite-tail-highest-error"),
                DeclarationHandle.Create(Module + ".matrixHermiteTail_highest_error"),
                H("Operator norm error with a within-derivative budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(DeBoor)),
                Blocks(
                    Paragraph(Text("In a nondegenerate closed interval let the three nodes "
                        + "be positive, with arbitrary repetitions. Suppose the matrix function "
                        + "has the form K + x³V₀ + x⁴V₁ + E(x) there, where K is constant. "
                        + "The remainder is twice continuously differentiable entrywise within "
                        + "the interval, and its within-derivative matrices of orders 1 and 2 "
                        + "have Euclidean operator norms bounded by B₀ and B₁.")),
                    Paragraph(Text("If the reported blocks differ from "), Ref(MatrixTail),
                        Text(" by at most ε in the maximum of the two operator norms, the "
                            + "quartic coefficient error is at most ε times the absolute row "
                            + "sum plus |w₀|B₀ + |w₁|B₁/2, where w₀ and w₁ are the two "
                            + "inverse weights. In particular, exact data recover V₁ when "
                            + "the remainder vanishes, for any K.")),
                    Paragraph(Text("The positive-order observations eliminate K. Testing the "
                        + "remainder block against two Euclidean vectors reduces each prefix "
                        + "to a scalar Hermite mean value identity. The resulting bound is "
                        + "B₀ for the first block and B₁/2 for the second."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matrix-hermite-tail-highest-attained"),
                DeclarationHandle.Create(Module + ".matrixHermiteTail_highest_attained"),
                H("Rank-one attainment of the direct noise term"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every such node triple, every constant K and every "
                    + "ε ≥ 0, take both coefficients along a rank-one matrix P of operator "
                    + "norm 1. A polynomial signal with remainder zero has exact data "
                    + "(−εP, εP) and quartic coefficient ε times the absolute row sum "
                    + "times P. With reported data zero, the direct noise is ε and the "
                    + "operator norm of the coefficient error attains the direct noise bound."))),
                DescribeRole.Theorem))));
}
