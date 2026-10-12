using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class MatrixSimilarityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eigenvalues under unitary similarity.", H("MatrixSimilarity"), Blocks(
            Paragraph(Text("A Hermitian matrix unitarily similar to a real diagonal matrix has the same eigenvalues up to a permutation. The characteristic polynomial and its roots provide the spectral identification used for compound matrices.")),
            Paragraph(Text("The source is Alex Meiburg's Apache-2.0 Physlib at revision "
                + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142. These results support the "
                + "Schatten product Holder inequality. No mathematical originality is claimed.")))));
}
