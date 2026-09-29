using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class MostowPrasadRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/MostowPrasadRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The metric uniqueness interface for the Mostow--Prasad rigidity endpoint.",
        H("Mostow--Prasad rigidity: metric uniqueness interface"),
        Blocks(
            Paragraph(Text(
                "The first reusable interface for the Mostow--Prasad endpoint is the metric "
                    + "uniqueness principle: an isometry equivalence is determined by its values "
                    + "on a dense subset. The full theorem requires additional hyperbolic geometry "
                    + "and is not claimed by this module.")),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-dense-uniqueness"),
                DeclarationHandle.Create(Prefix + "isometry_equiv_eq_of_eqOn_dense"),
                H("Dense-set uniqueness of isometries"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two isometry equivalences that agree on a dense subset of the source "
                        + "are equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-dense-range-uniqueness"),
                DeclarationHandle.Create(Prefix + "isometry_equiv_eq_of_dense_range"),
                H("Dense-range uniqueness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same uniqueness result accepts a dense parametrization directly."))),
                DescribeRole.Theorem)),
        []));
}
