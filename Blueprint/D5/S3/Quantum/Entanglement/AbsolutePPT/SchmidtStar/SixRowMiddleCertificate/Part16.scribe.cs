using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate;
internal sealed class Part16Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each frozen leaf has a positive epsilon=-max(b)/2 and a positive integer denominator clearer C. The identity C*(-P-epsilon)=tensor4 is proved by ordinary ring normalization. Closed left and right children retain their common face; all leaves in this subtree are consumed.", H("Part16"), Blocks(
            Paragraph(Text("Each frozen leaf has a positive epsilon=-max(b)/2 and a positive integer denominator clearer C. The identity C*(-P-epsilon)=tensor4 is proved by ordinary ring normalization. Closed left and right children retain their common face; all leaves in this subtree are consumed.")),
            Describe.Lean(DescribeId.Create("sixrowmiddlecertificate-part16-exclude-00"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part16.exclude_00"),
                H("exclude_00"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The eight necessary inequalities contradict this closed subtree's coordinate bounds."))), DescribeRole.Theorem)
        )));
}
