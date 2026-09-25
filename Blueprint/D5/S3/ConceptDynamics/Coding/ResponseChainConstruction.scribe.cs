using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResponseChainConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite sequence of numbered response decompositions constructs the matrix chain and its additive-window path conjugacy.",
        H("Numbered response chains"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("numbered-response-chain-window"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseChainConstruction.numbered_response_chain_has_window_conjugacy"),
                H("Response decompositions build a finite chain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each step stores a bijection between the actual numbered edges and its two factor edges through a middle response state. Counting each bijection supplies the product identity at that step. Induction then gives the complete strong shift equivalence chain, and composing the elementary path recodings yields a conjugacy whose observation windows add the number of response steps."))),
                DescribeRole.Theorem))));
}
