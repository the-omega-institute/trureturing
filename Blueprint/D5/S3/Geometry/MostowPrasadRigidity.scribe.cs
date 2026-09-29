using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class MostowPrasadRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/MostowPrasadRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The metric and group-conjugacy interfaces for the Mostow--Prasad rigidity endpoint.",
        H("Mostow--Prasad rigidity: metric and group interfaces"),
        Blocks(
            Paragraph(Text(
                "The reusable interfaces for the Mostow--Prasad endpoint include metric uniqueness "
                    + "and the algebraic statement that holonomy representations are related by "
                    + "conjugacy in an ambient group. The full theorem requires additional "
                    + "hyperbolic geometry and is not claimed by this module.")),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-group-conjugacy"),
                DeclarationHandle.Create(Prefix + "GroupConjugacy"),
                H("Group conjugacy interface"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An abstract group isomorphism is realized by conjugacy in an ambient group."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-group-conjugacy-symm"),
                DeclarationHandle.Create(Prefix + "groupConjugacy_symm"),
                H("Symmetry of group conjugacy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The group-conjugacy relation is preserved by inverting the group isomorphism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-group-conjugacy-trans"),
                DeclarationHandle.Create(Prefix + "groupConjugacy_trans"),
                H("Composition of group conjugacy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Conjugacy certificates compose along group isomorphisms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mostow-prasad-group-conjugator-unique"),
                DeclarationHandle.Create(Prefix + "groupConjugacy_conjugator_unique"),
                H("Uniqueness of the conjugator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A trivial centralizer for the holonomy image makes the ambient conjugator unique."))),
                DescribeRole.Theorem)),
        []));
}
