using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class ExpandingGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expanding square matrices.", H("ExpandingGram"), Blocks(
            Paragraph(Text("A right Gram matrix bounded below by the identity is positive definite, so its determinant and hence the determinant of the original square matrix are units. A singular value decomposition transfers positivity of the Gram matrix minus the identity to the diagonal of squared singular values minus the identity, and then to the left Gram matrix.")),
            Paragraph(Text("Conjugating this left Gram inequality by any square matrix and applying sorted singular-value monotonicity to adjoints proves that right multiplication by an expanding matrix increases each sorted singular value. The comparison allows singular left factors and empty matrices.")))));
}
