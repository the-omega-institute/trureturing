using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class PartialTransposeTraceDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) => new Formula.Apply(Id(s), [.. a]);
    private static Formula All(string s, Formula t, Formula body) =>
        Seq(Forall, Sp, Open, Id(s), Colon, t, Close, Comma, Sp, body);

    public DocumentDefinition Create()
    {
        var product = Call("Product",Id("A"),Id("B"));
        Formula statement = Seq(
            Call("inner",Id("v"),Call("apply",Call("partialTranspose",Id("M")),Id("v"))),F.Eq,
            Call("trace",Call("multiply",Id("M"),Call("partialTranspose",Call("outer",Id("v"),Id("v"))))));
        statement = All("v",Call("Vector",product,Id("C")),statement);
        statement = All("M",Call("Matrix",product,Id("C")),statement);
        statement = All("B",Id("FiniteType"),statement);
        statement = All("A",Id("FiniteType"),statement);
        return DocumentDefinition.Create(ScribeNode.Create(
        "Finite product-coordinate trace duality for partial transpose.",
        H("Partial transpose and trace pairing"), Blocks(
            Describe.Lean(DescribeId.Create("partial-transpose-trace-duality"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/PartialTransposeTrace.partial_transpose_trace_duality"),
                H("Vector and trace duality"),
                StatementSource.FromAuthor(Disp(statement)),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let A and B be arbitrary finite types, M a complex square matrix indexed by A times B, and v a complex vector on the same product. With Gamma(M)_(a,b),(c,d)=M_(a,d),(c,b), the identity is v* Gamma(M) v = Tr(M Gamma(v v*)). The vector need not be normalized; M need not be Hermitian or positive. Empty carriers and unequal local dimensions are included.")),
                    Paragraph(Text("The bilinear identity Tr(Gamma(M) N)=Tr(M Gamma(N)) follows by interchanging the two B indices in the four finite sums. The vector identity then uses the standard matrix outer-product multiplication and trace identities. This supplies the trace bridge for fixed product-corner APPT tests and uses the existing partialTranspose convention."))),
                DescribeRole.Theorem))));
    }
}
