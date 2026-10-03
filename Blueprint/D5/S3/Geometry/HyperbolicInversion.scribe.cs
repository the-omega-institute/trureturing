using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class HyperbolicInversionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/HyperbolicInversion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary-centered inversion of hyperbolic upper half-space.",
        H("Hyperbolic inversion"),
        Blocks(
            Paragraph(Text(
                "Euclidean inversion about the boundary origin preserves positive height "
                    + "and the normalized upper-half-space distance in any real inner "
                    + "product horizontal space. It is an involutive isometric equivalence. "
                    + "This does not construct the ideal boundary, classify the full "
                    + "isometry group, or prove Mostow--Prasad rigidity.")),
            Describe.Lean(
                DescribeId.Create("hyperbolic-inverted-point"),
                DeclarationHandle.Create(Prefix + "invertedPoint"),
                H("Inverted upper-half-space point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive-height restriction of unit-radius Euclidean inversion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hyperbolic-inversion-distance"),
                DeclarationHandle.Create(Prefix + "hyperbolicDist_invertedPoint"),
                H("Distance preservation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Euclidean separation and the height geometric mean acquire the same reciprocal factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hyperbolic-inversion-equivalence"),
                DeclarationHandle.Create(Prefix + "inversion"),
                H("Involutive isometric equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Euclidean inversion squared is the identity on positive-height points."))),
                DescribeRole.Definition)),
        []));
}
