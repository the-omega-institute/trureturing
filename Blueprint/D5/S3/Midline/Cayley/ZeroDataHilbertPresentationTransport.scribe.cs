using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline.Cayley;

internal sealed class ZeroDataHilbertPresentationTransportDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Midline/Cayley/ZeroDataHilbertPresentationTransport.";

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "The unique zero-preserving reindexing lifts to a unitary transport of mirror Krein and Cayley geometry.",
            H("ZeroData Hilbert presentation transport"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("zero-data-hilbert-transport-intertwines-mirror"),
                    DeclarationHandle.Create(Module + "zeroHilbertPresentationUnitary_intertwines_mirror"),
                    H("The Hilbert transport intertwines mirror symmetry"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("T_{Z,Z'} J_Z"), Sp, EqualTo, Sp,
                        F.Id("J_{Z'} T_{Z,Z'}")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The coordinate equivalence is the unique zero-preserving reindexing lifted through analytic multiplicity fibers."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("zero-data-hilbert-transport-preserves-krein"),
                    DeclarationHandle.Create(Module + "zeroHilbertPresentationUnitary_preserves_krein"),
                    H("The Hilbert transport preserves the Krein form"),
                    StatementSource.FromAuthor(Disp(Seq(
                        F.Id("[T psi,T phi]_{J'}"), Sp, EqualTo, Sp,
                        F.Id("[psi,phi]_J")))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The same unitary also intertwines the zero Cayley operators, so the operator geometry is presentation independent."))),
                    DescribeRole.Theorem))));
    }
}
