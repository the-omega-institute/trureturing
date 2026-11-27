using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography.MUB;

internal sealed class BoundarySphereCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Directed ridge certificates imply four-dimensional spherical cap coverage.",
        H("Boundary sphere coverage from directed ridges"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mub-boundary-sphere-cover-soundness"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/MUB/BoundarySphereCover.sphereCovered"),
                H("Soundness of the directed-ridge cover checker"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An accepted list of integer caps and simplicial facets covers "
                        + "every positive-radius sphere over a lawful ordered field. "
                        + "For a direction, maximize the dual pairing over the finite facet "
                        + "list. A negative basis coefficient would make the corresponding "
                        + "directed neighbor improve this pairing. The squared dual norm "
                        + "then bounds the sum of the nonnegative coefficients by one, "
                        + "forcing a cap inequality.")),
                    Paragraph(Text(
                        "No global fan or completeness of convex-hull enumeration is a "
                        + "premise. A pinned atlas chart is a kernel-checked concrete "
                        + "application. Coverage does not imply transfer between charts "
                        + "or nonexistence of four mutually unbiased bases."))),
                DescribeRole.Theorem))));
}
