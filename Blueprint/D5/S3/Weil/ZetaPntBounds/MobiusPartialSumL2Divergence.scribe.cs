using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaPntBounds;

internal sealed class MobiusPartialSumL2DivergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal weighted Möbius partial-sum divergence.",
        H("Literal weighted Möbius partial-sum divergence"),
        Blocks(
            Paragraph(Text(
                "This unit keeps the literal finite sum over 1 ≤ n ≤ floor(x), with coefficient "
                + "the ordinary Möbius value divided by n, and the Lebesgue measure restricted to "
                + "the open half-line (1,∞). The proof uses the shifted Möbius Dirichlet series, "
                + "a general L² half-line Mellin pairing, and an unconditional nontrivial zeta-zero "
                + "witness. It does not assume RH or add a conditional certificate premise.")),
            Describe.Lean(DescribeId.Create("half-line-measure"),
                DeclarationHandle.Create(Prefix + "halfLineMeasure"),
                H("Half-line Lebesgue measure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The measure is volume restricted to Ioi 1, exactly the domain used by the "
                    + "literal MemLp conclusion."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literal-mobius-partial-sum"),
                DeclarationHandle.Create(Prefix + "mobiusPartialSum"),
                H("Literal weighted Möbius partial sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For real x the function sums the ordinary arithmetic Möbius coefficient over "
                    + "the finite integer interval 1 ≤ n ≤ floor(x), dividing each term by n. "
                    + "No abstract transform replaces this function."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("half-line-mellin"),
                DeclarationHandle.Create(Prefix + "halfLineMellin"),
                H("General half-line Mellin functional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For any complex-valued function and complex parameter s, this is the "
                    + "Bochner integral of f(x) times x to the power -(s+1) over Ioi 1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("half-line-mellin-norm-bound"),
                DeclarationHandle.Create(Prefix + "halfLineMellin_norm_le"),
                H("Sharp L² half-line Mellin norm bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Every MemLp-2 function on the half-line has Mellin functional norm at most "
                    + "its L² norm divided by sqrt(2 Re(s)+1), whenever Re(s)>-1/2. The proof "
                    + "computes the exact kernel energy and applies Cauchy–Schwarz."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("half-line-mellin-differentiable"),
                DeclarationHandle.Create(Prefix + "halfLineMellin_differentiableAt"),
                H("Local differentiability of the general Mellin functional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The Mellin functional is complex differentiable at every parameter in the "
                    + "half-plane Re(s)>-1/2. An integrable logarithmic derivative majorant supplies "
                    + "the local dominated-derivative argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("half-line-mellin-analytic"),
                DeclarationHandle.Create(Prefix + "halfLineMellin_analyticOnNhd"),
                H("Analyticity of the general Mellin functional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The same general L² functional is analytic on neighborhoods throughout the "
                    + "half-plane Re(s)>-1/2."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-mobius-divergence"),
                DeclarationHandle.Create(Prefix + "mobiusPartialSum_not_memLp"),
                H("Unconditional literal Möbius partial-sum L² divergence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem proves the exact unconditional negation of MemLp for the literal "
                    + "weighted Möbius partial sum on Ioi 1. The contradiction combines the shifted "
                    + "Möbius Dirichlet identity with analytic continuation of the product s·ζ(s+1) "
                    + "and the sharp half-line L² bound. A zero with real part at least one half is "
                    + "obtained unconditionally from the canonical zero data and reflection; the "
                    + "argument does not claim the Riemann hypothesis."))), DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZeroData/UnconditionalCanonicalZeroData"))
        ]));
}
