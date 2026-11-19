using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class VBKMWeightIdealDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/VertexAlgebra/Sectors/VBKMWeightIdeal";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/zveryk2026virasoroextensions");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Virasoro and Borcherds presentation, action, and ideal structure.",
        H("VBKMWeightIdeal"), Blocks(
        Describe.Lean(DescribeId.Create("zv-nonzero-disjoint-ideal"),
            DeclarationHandle.Create(Module + ".nonzero_disjoint_ideal"), H("nonzero disjoint ideal"),
            StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("N"), Sp, F.Id("P"), Sp, Colon, Sp, Q("Type"))), Comma, Sp, Seq(OpenBracket, Seq(Q("LieRing"), Sp, F.Id("A")), CloseBracket), Comma, Sp, Seq(OpenBracket, Seq(Q("LieAlgebra"), Sp, Complex, Sp, F.Id("A")), CloseBracket), Comma, Sp, Forall, Sp, Parenthesized(Seq(Q("neg"), Sp, Colon, Sp, F.Id("N"), Sp, To, Sp, F.Id("A"))), Comma, Sp, Forall, Sp, Parenthesized(Seq(Q("pos"), Sp, Colon, Sp, F.Id("P"), Sp, To, Sp, F.Id("A"))), Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, F.Id("H"), Sp, Colon, Sp, F.Id("A"))), Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("C"), Sp, Colon, Sp, Q("Set"), Sp, F.Id("A"))), Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("c"), Sp, InMacro, Sp, F.Id("C"), Comma, Sp, Forall, Sp, F.Id("n"), Comma, Sp, OpenBracket, Sp, F.Id("c"), Comma, Q("neg"), Sp, F.Id("n"), CloseBracket, Sp, InMacro, Sp, Q("Submodule","span"), Sp, Complex, Sp, Parenthesized(Seq(Q("Set","range"), Sp, Q("neg"))))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("c"), Sp, InMacro, Sp, F.Id("C"), Comma, Sp, OpenBracket, Sp, F.Id("c"), Comma, F.Id("v"), CloseBracket, Sp, InMacro, Sp, Q("Submodule","span"), Sp, Complex, Sp, Parenthesized(Seq(Seq(OpenBrace, F.Id("v"), CloseBrace), Sp, Colon, Sp, Q("Set"), Sp, F.Id("A"))))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("p"), Sp, F.Id("n"), Comma, Sp, OpenBracket, Sp, Q("pos"), Sp, F.Id("p"), Comma, Q("neg"), Sp, F.Id("n"), CloseBracket, Sp, InMacro, Sp, Q("sup"), Sp, Parenthesized(Seq(Q("sup"), Sp, Parenthesized(Seq(Q("Submodule","span"), Sp, Complex, Sp, Parenthesized(Seq(Q("Set","range"), Sp, Q("neg"))))), Sp, Parenthesized(Seq(Q("Submodule","span"), Sp, Complex, Sp, F.Id("C"))))), Sp, Parenthesized(Seq(Q("Submodule","span"), Sp, Complex, Sp, Parenthesized(Seq(Q("Set","range"), Sp, Q("pos"))))))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("p"), Comma, Sp, OpenBracket, Sp, Q("pos"), Sp, F.Id("p"), Comma, F.Id("v"), CloseBracket, Sp, Eq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(Q("LieSubalgebra","lieSpan"), Sp, Complex, Sp, F.Id("A"), Sp, Parenthesized(Seq(F.Id("C"), Sp, Cup, Sp, Q("Set","range"), Sp, Q("neg"), Sp, Cup, Sp, Q("Set","range"), Sp, Q("pos"))), Sp, Eq, Sp, Q("Top","top"), Sp)), Sp, To, Sp, Forall, Sp, Parenthesized(Seq(Alpha, Sp, Colon, Sp, F.Id("N"), Sp, To, Sp, Complex, Sp)), Comma, Sp, Forall, Sp, Parenthesized(Seq(Mu, Sp, Colon, Sp, Complex, Sp)), Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Comma, Sp, OpenBracket, Sp, F.Id("H"), Comma, Q("neg"), Sp, F.Id("n"), CloseBracket, Sp, Eq, Sp, Parenthesized(Seq(Minus, Alpha, Sp, F.Id("n"))), Sp, Cdot, Sp, Q("neg"), Sp, F.Id("n"))), Sp, To, Sp, Parenthesized(Seq(OpenBracket, Sp, F.Id("H"), Comma, F.Id("v"), CloseBracket, Sp, Eq, Sp, Mu, Sp, Cdot, Sp, F.Id("v"))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Comma, Sp, D(0), Sp, Lt, Sp, Parenthesized(Seq(Alpha, Sp, F.Id("n"))), Dot, Q("re"))), Sp, To, Sp, Parenthesized(Seq(Mu, Sp, Dot, Q("re"), Sp, Lt, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(Forall, Sp, F.Id("c"), Sp, InMacro, Sp, F.Id("C"), Comma, Sp, OpenBracket, Sp, F.Id("H"), Comma, F.Id("c"), CloseBracket, Sp, Eq, Sp, D(0))), Sp, To, Sp, Parenthesized(Seq(F.Id("v"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Exists, Sp, F.Id("K"), Sp, Colon, Sp, Q("LieIdeal"), Sp, Complex, Sp, F.Id("A"), Comma, Sp, F.Id("K"), Sp, Neq, Sp, Perp, Sp, Land, Sp, Q("inf"), Sp, Q("K","toSubmodule"), Sp, Parenthesized(Seq(Q("Submodule","span"), Sp, Complex, Sp, F.Id("C"))), Sp, Eq, Sp, Perp, Sp))),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text("The displayed identity specifies nonzero disjoint ideal."))), DescribeRole.Theorem))));

    private static Formula Q(params string[] names) => Seq([.. names.SelectMany(
        (name, index) => index == 0
            ? new Formula[] { Operatorname, Grp(F.Id(name)) }
            : [Dot, Operatorname, Grp(F.Id(name))])]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
}
