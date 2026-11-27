using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Groups;

internal sealed class ValuationPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Valuation Pair", H("Valuation Pair"),
        Blocks(
            Paragraph(Text("Unitary group of a form over a star ring; integral, congruence subgroups; topology instances. Abstract Heisenberg bicharacter, representation, vacuum function and group action with cocycle. Twisted norm and its basic laws, tame cyclic actions, profinite rings. Ring pairs behaving as valuation rings after patching along idempotents.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Groups/ValuationPair.isClosedEmbedding_mat"),
                H("isClosedEmbedding_mat"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For invertible J over a Hausdorff topological commutative ring with continuous involution, the map sending an element of U(J) to its matrix is a closed embedding.")))))));
}
