using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Icosahedral;

internal sealed class ExteriorSquareRepresentationsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Icosahedral/ExteriorSquareRepresentations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two Hodge eigenspaces carry conjugate real A5 representations and split the wedge.",
        H("Icosahedral Hodge Representations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-hodge-projection"),
                DeclarationHandle.Create(Prefix + "positiveProjection"),
                H("The positive Hodge projector selects one eigenspace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive spectral projector selects the square-root-of-five Hodge "
                    + "eigenspace that carries one A5 representation."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("negative-hodge-projection"),
                DeclarationHandle.Create(Prefix + "negativeProjection"),
                H("The negative Hodge projector selects the conjugate eigenspace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The negative spectral projector selects the conjugate Hodge eigenspace "
                    + "that carries the second A5 representation."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("quadratic-galois-conjugacy-carrier"),
                DeclarationHandle.Create(Prefix + "RepresentationsAreQ5GaloisConjugate"),
                H("One quadratic action has two conjugate real embeddings"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier records a single exact matrix family over Q of square root "
                    + "five whose two embeddings give the two real coordinate actions."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("equivariant-hodge-decomposition"),
                DeclarationHandle.Create(Prefix + "exteriorSquareDecomposition"),
                H("The exterior square is explicitly the product of its Hodge eigenspaces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Spectral projectors and the coordinate equivalence assemble an explicit "
                    + "A5-equivariant product decomposition."))),
                DescribeRole.Definition
            )),
        []));
}
