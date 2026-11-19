using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips;
internal sealed class SignedFibresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each complementary-pair row has independent signed lifts.", H("Constant signed fibres"),
        Blocks(Describe.Lean(DescribeId.Create("sum-beta"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/SignedFibres.sum_beta"),
            H("Weighted sum over signed lifts"), StatementSource.FromAuthor(Disp(All("k", Call("Nat"), All("w", new Formula.TypeArrow(Parenthesized(new Formula.TypeArrow(Call("Fin", V("k")), Call("Fin", Num("4")))), Call("Int")), Eq(SumOver("c", new Formula.TypeArrow(Call("Fin", V("k")), Call("Fin", Num("8"))), App(V("w"), Parenthesized(Seq(Call("HardinA233196Strip.beta"), Sp, Circ, Sp, V("c"))))), new Formula.Binary(Parenthesized(new Formula.Power(Typed(Num("2"), Call("Int")), V("k"))), FormulaBinaryOperator.Multiply, Parenthesized(SumOver("r", new Formula.TypeArrow(Call("Fin", V("k")), Call("Fin", Num("4"))), App(V("w"), V("r")))))))))),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229750")),
            Blocks(Paragraph(Text("For every natural width k, each function r from Fin k to Fin 4 has exactly 2^k preimages under pointwise beta. The scalar count is two for each of the four complementary colour pairs. Fintype.card_piFinset multiplies these independent choices. Finset.sum_fiberwise then groups any integer weight by its raw boundary. In particular the factors are eight at width three and sixteen at width four. No row-legality assumption is needed for the fibre count."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string s)
    {
        var parts = s.Split('_');
        Formula Word(string p) => Seq(p.Select(ch => ch >= '0' && ch <= '9'
            ? Num(new string(new[] { ch })) : V(new string(new[] { ch }))).ToArray());
        Formula result = Word(parts[^1]);
        for (var i = parts.Length - 2; i >= 0; --i)
            result = Seq(Word(parts[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula All(string x, Formula t, Formula b) => Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x), t)), Sp, Parenthesized(b));

}
