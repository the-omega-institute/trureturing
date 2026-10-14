using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.RelativePairing;

internal sealed class RotatedAntighostAdjointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/RelativePairing/RotatedAntighostAdjoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native energy rotation cancels the opposite-mode antighost transpose phase.",
        H("Rotated antighost transpose"),
        Blocks(
            Paragraph(Text("The ghost carrier is the full finite-support exterior bc Fock space over the complex numbers. The pairing is Gplus(left,right)=BPZ(left,rotation(right)), where rotation has the original integer conformal-energy phase. Hplus conjugates the left argument. Pi is the actual occupation-parity operator. No mode cutoff or replacement pairing is used.")),
            Describe.Lean(DescribeId.Create("rotated-antighost-bilinear"),
                DeclarationHandle.Create(Prefix + "Gplus_b"), H("Bilinear opposite-mode transpose"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer mode, Gplus(b(mode) left,right)=Gplus(Pi left,b(-mode) right). The BPZ factor (-1)^mode and the rotation factor for the opposite mode coincide, giving this positive transpose sign."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rotated-antighost-sesquilinear"),
                DeclarationHandle.Create(Prefix + "Hplus_b"), H("Conjugate-left opposite-mode transpose"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Coefficient conjugation commutes with b and Pi, hence Hplus(b(mode) left,right)=Hplus(Pi left,b(-mode) right). Tensoring this identity with the actual matter form supplies the antighost transpose needed for relative-kernel isotropy."))), DescribeRole.Theorem))));
}
