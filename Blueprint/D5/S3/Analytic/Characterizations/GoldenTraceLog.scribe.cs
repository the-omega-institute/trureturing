using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Characterizations;

internal sealed class GoldenTraceLogDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Characterizations/GoldenTraceLog.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual golden adjacency trace series converges absolutely on its open disk and gives a justified principal logarithm.",
        H("Golden Trace Logarithm"),
        Blocks(
            Paragraph(Text(
                "The source is Part1739 of OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY. "
                    + "The positive exponential of the infinite trace series is a reciprocal "
                    + "determinant, also commonly called a dynamical zeta. The logarithm identity "
                    + "for a two-by-two matrix uses two spectral values satisfying its trace "
                    + "and determinant equations.")),
            Describe.Lean(DescribeId.Create("actual-adjacency"),
                DeclarationHandle.Create(Prefix + "adjacency"), H("Actual adjacency"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The adjacency is the entrywise complex image of the real Fibonacci "
                        + "substitution matrix. Both off-diagonal entries and the first diagonal "
                        + "entry are one; the second diagonal entry is zero. False and true "
                        + "letters correspond to the first and second states."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trace-term"),
                DeclarationHandle.Create(Prefix + "traceTerm"), H("Positive-index trace term"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The natural index is shifted by one, so the defining series has exactly "
                        + "the positive indices. The trace belongs to the actual "
                        + "matrix power, and the denominator and power of the complex variable "
                        + "have the same positive index."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("local-domain"),
                DeclarationHandle.Create(Prefix + "localDomain"), H("Local convergence domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The open complex disk has radius the reciprocal of the positive golden "
                        + "ratio. Neither boundary point nor exterior point belongs to the "
                        + "domain of this series-defined function."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("trace-sum"),
                DeclarationHandle.Create(Prefix + "traceSum"), H("Infinite trace sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sum is defined on the subtype of the local disk. The trace series is "
                        + "absolutely summable and has the sum given by the local logarithm identity "
                        + "at every input. A totalized sum at a point of divergence does not "
                        + "define this analytic function."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("local-zeta"),
                DeclarationHandle.Create(Prefix + "dynamicalZeta"), H("Positive exponential"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function is the exponential of the infinite trace sum with a positive "
                        + "sign in the exponent. Its domain is the local disk."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rational-continuation"),
                DeclarationHandle.Create(Prefix + "continuation"), H("Separate rational continuation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This rational expression agrees with the local exponential on the disk. "
                        + "Totalized complex division assigns finite values at denominator zeros, "
                        + "but the pole statements concern punctured meromorphic germs. They "
                        + "do not concern an exponential evaluated at a divergent series."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("local-contract"),
                DeclarationHandle.Create(Prefix + "localContract"), H("Local analytic contract"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The determinant and golden factorization hold for every complex variable, "
                        + "and the trace formula holds at every natural power. On the local disk, "
                        + "the determinant has positive real part and is nonzero; the trace series "
                        + "is absolutely summable and has sum equal to the negative principal "
                        + "logarithm of the determinant, and the positive exponential equals "
                        + "the rational continuation. "
                        + "The logarithm representative is analytic and normalized at zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("absolute-log-summability"),
                DeclarationHandle.Create(Prefix + "summable_norm_log_terms"), H("Absolute logarithm summability"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every complex input of norm less than one, the positive-index "
                        + "logarithm terms are absolutely summable by geometric domination. "
                        + "The same bound controls the correction at the golden convergence boundary."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("two-root-producer"),
                DeclarationHandle.Create(Prefix + "matrix_trace_log"), H("Two-root logarithm identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a complex two-by-two matrix with the supplied Vieta trace and determinant, "
                        + "both scaled roots must have norm less than one. Scalar logarithm series "
                        + "then give the actual infinite HasSum. The two factors have positive real "
                        + "parts, so their principal arguments have sum strictly between minus pi "
                        + "and pi. This discharges the product-log branch before exponentiation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("golden-local"),
                DeclarationHandle.Create(Prefix + "golden_local"), H("Golden local identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The trace and determinant of the golden adjacency satisfy the two-root "
                        + "hypotheses. A norm estimate keeps the determinant in the open right "
                        + "half-plane throughout the entire stated disk. Thus the principal "
                        + "logarithm identity holds on this local branch. Nonvanishing alone "
                        + "does not imply a global unwrapped logarithm identity."))), DescribeRole.Theorem))));
}
