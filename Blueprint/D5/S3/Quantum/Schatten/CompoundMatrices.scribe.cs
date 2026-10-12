using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class CompoundMatricesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compound matrices and singular products.", H("CompoundMatrices"), Blocks(
            Paragraph(Text("The kth compound matrix has entries equal to kth order minors. Cauchy-Binet makes the compound construction multiplicative. Unitary diagonalization identifies its singular values with products over kth order subsets; sorting identifies the largest such product.")),
            Paragraph(Text("The source is Alex Meiburg's Apache-2.0 Physlib at revision "
                + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142. These results support the "
                + "Schatten product Holder inequality. No mathematical originality is claimed.")))));
}
