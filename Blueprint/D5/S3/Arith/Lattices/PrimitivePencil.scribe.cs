using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class PrimitivePencilDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every full row rank integer matrix admits one perturbation with primitive maximal minors for all integer parameters.",
        H("PrimitivePencil"),
        Blocks(
            Describe.Lean(DescribeId.Create("primitive-pencil-perturbation"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/PrimitivePencil.primitive_pencil_perturbation"),
                H("primitive pencil perturbation"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Comma, Sp, Seq(Parenthesized(Seq(Call("Function"), Sp, Dot, Sp, Call("Injective"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("x"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("d"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Mapsto, Sp, F.Id("A"), Sp, Dot, Sp, Call("transpose"), Sp, new Formula.Subscript(Star, F.Id("v")), Sp, F.Id("x"))))), Sp, To, Sp, Seq(Exists, Sp, F.Id("B"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Comma, Sp, Forall, Sp, F.Id("t"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Comma, Sp, Call("Finset"), Sp, Dot, Sp, Call("univ"), Sp, Dot, Sp, Call("gcd"), Sp, Parenthesized(Seq(Call("cofactor"), Sp, Parenthesized(Seq(F.Id("t"), Sp, Cdot, Sp, F.Id("A"), Sp, Plus, Sp, F.Id("B"))))), Sp, Eq, Sp, D(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every full row rank integer matrix admits one perturbation with primitive maximal minors for all integer parameters."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name) => Seq(Operatorname, Grp(F.Id(name)));
}
