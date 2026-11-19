using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips;
internal sealed class TableBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/TableBridge.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229752");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite data support the literal width-five king-grid recurrence.", H("Two-defect king transfers"),
        Blocks(
            Describe.Lean(DescribeId.Create("count-successors"),
                DeclarationHandle.Create(Prefix + "count_successors"), H("A sorted successor list supplies all multiplicities"),
                StatementSource.FromAuthor(Disp(All("q", Call("Nat"), All("k", Call("Nat"), All("M", Call("Nat"), All("P", Arrow(Call("DefectTransfer.Row", V("q"), V("k")), Call("Prop")), Instance(Call("DecidablePred", V("P")), All("c", Arrow(Call("DefectTransfer.Row", V("q"), V("k")), Call("Fin", V("M"))), All("s", Call("Fin", V("M")), Eq(Call("List.count", V("s"), Call("List.insertionSort", Lam("a", Call("Fin", V("M")), Lam("b", Call("Fin", V("M")), Leq(V("a"), V("b")))), Call("List.filterMap", Lam("r", Call("DefectTransfer.Row", V("q"), V("k")), Conditional(Call("P", V("r")), Call("some", Call("c", V("r"))), Call("none"))), Call("List.ofFn", Lam("i", Call("Fin", Pow(V("q"), V("k"))), Call("Equiv.symm", Call("finFunctionFinEquiv"), V("i"))))))), SumOver("r", Call("DefectTransfer.Row", V("q"), V("k")), Conditional(And(Call("P", V("r")), Eq(Call("c", V("r")), V("s"))), Num("1"), Num("0"))))))))))))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For arbitrary palette q, width k, class size M, decidable admissibility P, classifier c and class s, the count of s in the sorted filtered enumeration equals the sum over rows of the indicator of P(r) and c(r)=s. The enumeration uses Mathlib finFunctionFinEquiv; insertion sorting preserves multiplicity."))), DescribeRole.Theorem))));

    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
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
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula SumOver(string x, Formula t, Formula b) => Seq(Sum, Underscore, Grp(Typed(V(x), t)), Sp, Parenthesized(b));
    private static Formula Conditional(Formula a, Formula b, Formula c) => Parenthesized(Seq(Q("if"), Sp, a, Sp, Q("then"), Sp, b, Sp, Q("else"), Sp, c));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Lam(string x, Formula t, Formula b) => Seq(LambdaLower, Sp, Typed(V(x), t), Sp, Mapsto, Sp, Parenthesized(b));

}
