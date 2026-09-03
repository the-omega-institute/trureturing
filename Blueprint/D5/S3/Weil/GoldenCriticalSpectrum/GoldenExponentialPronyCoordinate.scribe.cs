using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GoldenCriticalSpectrum;

internal sealed class GoldenExponentialPronyCoordinateDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The split golden sampling atom is a nonvanishing complex character: "
            + "addition of lifted displacements becomes multiplication of Prony nodes, "
            + "natural translation becomes powers, and radius records the real displacement.",
        H("Golden Exponential Prony Coordinate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-exponential-coordinate-is-the-sampling-atom"),
                DeclarationHandle.Create(
                    Prefix + "golden_exponential_prony_coordinate_eq_sampling_atom"),
                H("The complex coordinate equals the existing golden sampling atom"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Packaging a complex displacement by its real and imaginary parts reproduces the repository's existing radial-phase golden sampling atom exactly.")),
                    Paragraph(Text(
                        "This theorem prevents a second sampling convention and fixes the sign of both radial damping and phase rotation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-exponential-coordinate-additive-character"),
                DeclarationHandle.Create(
                    Prefix + "golden_exponential_prony_coordinate_add"),
                H("Lifted addition becomes multiplication of Prony nodes"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The golden exponential coordinate is an additive-to-multiplicative character on the lifted complex displacement plane.")),
                    Paragraph(Text(
                        "Consequently, independent shifts compose without introducing a second transport law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-exponential-coordinate-natural-time-powers"),
                DeclarationHandle.Create(
                    Prefix + "golden_exponential_prony_coordinate_nat_mul"),
                H("Natural translation depth becomes ordinary powers"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Sampling a lifted displacement after a natural number of equal steps gives the corresponding ordinary power of the one-step node.")),
                    Paragraph(Text(
                        "This is the exact time-character law required by finite Prony and Vandermonde reconstruction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-exponential-coordinate-radius-and-alias-boundary"),
                DeclarationHandle.Create(
                    Prefix + "golden_exponential_prony_coordinate_eq_implies_re_eq"),
                H("Node equality preserves radial displacement"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equal golden exponential nodes have equal real coordinates because their norms are injective real exponentials of the radial displacement.")),
                    Paragraph(Text(
                        "Any unresolved collision is therefore purely vertical phase aliasing. No global imaginary-direction injectivity is claimed."))),
                DescribeRole.Theorem))));
}
