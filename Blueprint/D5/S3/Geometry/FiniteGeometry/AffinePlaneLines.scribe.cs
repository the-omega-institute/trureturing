using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGeometry;

internal sealed class AffinePlaneLinesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-field affine lines through a point are indexed by slopes and one vertical direction.",
        H("Affine Lines over a Finite Field"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("affine-lines-through-a-point-have-field-cardinality-plus-one"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/FiniteGeometry/AffinePlaneLines.card_affineLines_through"),
                H("A point lies on field-cardinality plus one affine lines"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite field F and a point p in F x F, the graph lines "
                    + "y = m x + b are indexed by m in F, and one additional vertical "
                    + "line x = p.1 passes through p. The resulting finite set has "
                    + "cardinality Fintype.card F + 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinct-points-determine-a-unique-affine-line"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/FiniteGeometry/AffinePlaneLines.exists_unique_line_through_distinct_points"),
                H("Two distinct points determine one affine line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For distinct points, equal first coordinates force the unique vertical "
                    + "line; unequal first coordinates determine the unique slope and intercept "
                    + "by field division. The Lean proof covers both cases explicitly."))),
                DescribeRole.Theorem)),
        []));
}
