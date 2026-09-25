using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FirstResponseDiamondDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal first-level row and column classes construct an explicit quotient diamond.",
        H("First response diamond"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("first-response-diamond"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FirstResponseDiamond.first_response_diamond"),
                H("First response row and column diamond"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Equal-column and equal-row response classes determine a common matrix from class representatives. Their membership and representative matrices recover the original graph, while the class-intersection matrix and the common matrix give an explicit elementary strong shift equivalence between the two first quotients. The factorization is derived from the row and column properties."))),
                DescribeRole.Theorem))));
}
