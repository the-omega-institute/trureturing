using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class VBKMPrimitiveKernelDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/VertexAlgebra/Sectors/VBKMPrimitiveKernel";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/zveryk2026virasoroextensions");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Virasoro and Borcherds presentation, action, and ideal structure.",
        H("VBKMPrimitiveKernel"), Blocks(
        Describe.Lean(DescribeId.Create("zv-normalized-not-proper"),
            DeclarationHandle.Create(Module + ".normalized_not_proper"), H("normalized not proper"),
            StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, F.Id("L"), Sp, Colon, Sp, Q("Type"))), Comma, Sp, Seq(OpenBracket, Seq(Q("AddCommGroup"), Sp, F.Id("M")), CloseBracket), Comma, Sp, Seq(OpenBracket, Seq(Q("Module"), Sp, Complex, Sp, F.Id("M")), CloseBracket), Comma, Sp, Seq(OpenBracket, Seq(Q("LieRing"), Sp, F.Id("L")), CloseBracket), Comma, Sp, Seq(OpenBracket, Seq(Q("LieAlgebra"), Sp, Complex, Sp, F.Id("L")), CloseBracket), Comma, Sp, Seq(OpenBracket, Seq(Q("LieRingModule"), Sp, F.Id("L"), Sp, F.Id("M")), CloseBracket), Comma, Sp, Seq(OpenBracket, Seq(Q("LieModule"), Sp, Complex, Sp, F.Id("L"), Sp, F.Id("M")), CloseBracket), Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("H"), Sp, F.Id("E"), Sp, F.Id("F"), Sp, Colon, Sp, F.Id("L"))), Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("b"), Sp, Colon, Sp, Complex, Sp)), Comma, Sp, Parenthesized(Seq(F.Id("a"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(OpenBracket, Sp, F.Id("E"), Comma, F.Id("F"), CloseBracket, Sp, Eq, Sp, F.Id("H"))), Sp, To, Sp, Parenthesized(Seq(OpenBracket, Sp, F.Id("H"), Comma, F.Id("E"), CloseBracket, Sp, Eq, Sp, F.Id("a"), Sp, Cdot, Sp, F.Id("E"))), Sp, To, Sp, Parenthesized(Seq(OpenBracket, Sp, F.Id("H"), Comma, F.Id("F"), CloseBracket, Sp, Eq, Sp, Minus, F.Id("a"), Sp, Cdot, Sp, F.Id("F"))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("w"), Sp, F.Id("x"), Sp, Colon, Sp, F.Id("M"))), Comma, Sp, Parenthesized(Seq(OpenBracket, Sp, F.Id("H"), Comma, F.Id("w"), CloseBracket, Sp, Eq, Sp, F.Id("b"), Sp, Cdot, Sp, F.Id("w"))), Sp, To, Sp, Parenthesized(Seq(OpenBracket, Sp, F.Id("E"), Comma, F.Id("w"), CloseBracket, Sp, Eq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Natural, Sp, Comma, Sp, Parenthesized(Seq(D(2), Slash, F.Id("a"))), Star, F.Id("b"), Sp, Neq, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Complex, Sp)))), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, Q("Set"), Sp, F.Id("L"))), Comma, Sp, Parenthesized(Seq(F.Id("S"), Sp, Subseteq, Sp, Q("Submodule","span"), Sp, Complex, Sp, Parenthesized(Seq(Seq(OpenBrace, Seq(F.Id("E"), Comma, F.Id("F"), Comma, F.Id("H")), CloseBrace), Sp, Colon, Sp, Q("Set"), Sp, F.Id("L"))))), Sp, To, Sp, Parenthesized(Seq(F.Id("x"), Sp, InMacro, Sp, Q("LieSubmodule","lieSpan"), Sp, Complex, Sp, Parenthesized(Seq(Q("LieSubalgebra","lieSpan"), Sp, Complex, Sp, F.Id("L"), Sp, F.Id("S"))), Sp, Parenthesized(Seq(Seq(OpenBrace, F.Id("w"), CloseBrace), Sp, Colon, Sp, Q("Set"), Sp, F.Id("M"))))), Sp, To, Sp, Parenthesized(Seq(OpenBracket, Sp, F.Id("E"), Comma, F.Id("x"), CloseBracket, Sp, Eq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(F.Id("x"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Neg, Sp, Parenthesized(Seq(Q("LieSubmodule","lieSpan"), Sp, Complex, Sp, Parenthesized(Seq(Q("LieSubalgebra","lieSpan"), Sp, Complex, Sp, F.Id("L"), Sp, F.Id("S"))), Sp, Parenthesized(Seq(Seq(OpenBrace, F.Id("x"), CloseBrace), Sp, Colon, Sp, Q("Set"), Sp, F.Id("M"))))), Dot, Q("toSubmodule"), Sp, Lt, Sp, Parenthesized(Seq(Q("LieSubmodule","lieSpan"), Sp, Complex, Sp, Parenthesized(Seq(Q("LieSubalgebra","lieSpan"), Sp, Complex, Sp, F.Id("L"), Sp, F.Id("S"))), Sp, Parenthesized(Seq(Seq(OpenBrace, F.Id("w"), CloseBrace), Sp, Colon, Sp, Q("Set"), Sp, F.Id("M"))))), Dot, Q("toSubmodule")))),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text("The displayed identity specifies normalized not proper."))), DescribeRole.Theorem))));

    private static Formula Q(params string[] names) => Seq([.. names.SelectMany(
        (name, index) => index == 0
            ? new Formula[] { Operatorname, Grp(F.Id(name)) }
            : [Dot, Operatorname, Grp(F.Id(name))])]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));
}
