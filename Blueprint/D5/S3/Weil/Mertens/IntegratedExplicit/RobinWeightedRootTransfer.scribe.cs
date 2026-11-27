using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RobinWeightedRootTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/IntegratedExplicit/RobinWeightedRootTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact power main term and logarithmic correction for the Robin weight.",
        H("Logarithmic correction for the weighted Robin tail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("power-main-term"),
                DeclarationHandle.Create(Prefix + "power_main_eq"),
                H("Exact main term with the inverse-logarithm correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For r less than j and u positive, split H(j,v) into j/(j-r) times "
                    + "H(j-r,v) and the correction -r/((j-r)v²). The exponential times "
                    + "the first weight integrates exactly to exp((r-j)u)/u before "
                    + "multiplication by j/(j-r). The remaining integral retains the v⁻² factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inverse-square-tail-bounds"),
                DeclarationHandle.Create(Prefix + "exponential_inverse_square_tail_bounds"),
                H("Two bounds for the inverse-logarithm correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive a and u, the integral of exp(-av)/v² over v greater than u "
                    + "lies between exp(-au)/(a(u+1/a)²) and exp(-au)/(au²). The upper bound "
                    + "uses v at least u. For the lower bound, the affine tangent to v⁻² at u+1/a "
                    + "has the same exponential integral as its constant term because the centered "
                    + "first moment vanishes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("square-root-main-term"),
                DeclarationHandle.Create(Prefix + "square_root_power_main_bounds"),
                H("Bounds for the square-root main term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At j = 1 and power 1/2, both bounds subtract a positive correction "
                    + "from 2 exp(-u/2)/u. The upper bound subtracts "
                    + "2 exp(-u/2)/(u+2)², which improves the finite range estimate "
                    + "for the prime-power correction."))),
                DescribeRole.Theorem))));
}
