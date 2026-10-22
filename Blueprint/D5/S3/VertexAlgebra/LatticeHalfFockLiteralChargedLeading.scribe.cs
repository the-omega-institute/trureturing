using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockLiteralChargedLeadingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockLiteralChargedLeading.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original charged leading coefficients and ordinary source modes", H("Two Literal Leading Charts"), Blocks(
            Paragraph(Text("Write g=B(a,b), N=natAbs(g), rPlus=(N+g).toNat and rMinus=(N-g).toNat. The fields, localPlus and localMinus are the original ones. Every signed pairing, including zero, is allowed; hu:IsUnit D.G.det is the original native ground hypothesis. Targets are arbitrary actual oscillator tensors.")),
            Describe.Lean(DescribeId.Create("literal-plus-original-source"),
                DeclarationHandle.Create(Prefix + "literal_plus_original_source"), H("Plus chart"),
                StatementSource.FromAuthor(Disp(Call("LiteralPlusOriginalSource", F.Id("D"), F.Id("hu"), F.Id("a"), F.Id("b"), F.Id("M"), F.Id("v")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("localPlus(rPlus,M)v is exactly the coefficient M-2rPlus of Ytw applied to the original ordinary mode (Y(e_a)[[-g-1]])e_b. Here e_a is Finsupp.single a 1. The ordinary mode is epsilon(a,b)e_(a+b). Native chargeScalar factors and the leading 2^(-2g) combine to chargeScalar(a+b), with the full original ground multiplication retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-minus-original-source"),
                DeclarationHandle.Create(Prefix + "literal_minus_original_source"), H("Minus chart"),
                StatementSource.FromAuthor(Disp(Call("LiteralMinusOriginalSource", F.Id("D"), F.Id("hu"), F.Id("a"), F.Id("b"), F.Id("M"), F.Id("v")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("localMinus(rMinus,M)v is exactly the coefficient M-2rMinus of Ytw applied to (Y(e_(-a))[[g-1]])e_b. The original (-1)^E coordinate monodromy changes the charge to -a, and the plus identity applies without any sign restriction. These are first nonzero coefficients only; all-j identities, full twisted Jacobi, moonshine and the string/AdS bridge remain separate open obligations."))), DescribeRole.Theorem))));
}
