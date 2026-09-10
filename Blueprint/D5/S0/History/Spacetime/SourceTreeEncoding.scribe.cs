using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class SourceTreeEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Free binary source trees have precisely the independently generated tagged HF codes.",
        H("Source Tree Representation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("source-grammar-reconstruction"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/SourceTreeEncoding.sourceCode_full"),
                H("Every legal source code reconstructs a tree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction over the independent HF grammar reconstructs a FreeMagma Nat tree. "
                    + "Leaf and branch tags differ. Repeated natural leaves refer to the same source identifier, "
                    + "and event occurrence tags do not rename these leaves."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-tree-code-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/SourceTreeEncoding.source_code_equiv"),
                H("An exact representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The grammar reconstruction and injectivity proofs give both round trips. "
                    + "The carrier reuses Mathlib's free magma and the fixed HF pairing representation."))),
                DescribeRole.Definition))));
}
