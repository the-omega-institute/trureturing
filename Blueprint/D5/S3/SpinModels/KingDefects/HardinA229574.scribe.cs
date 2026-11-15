using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpinModels.KingDefects;

internal sealed class HardinA229574Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/SpinModels/KingDefects/HardinA229574.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229574");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: HardinA229574"),
        Blocks(
            Node("result", "The width-4 recurrence", Formula0(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The four-step recurrence holds for all natural heights n>7, with the width fixed at 4. Counts are cast to integers before subtraction."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Formula0() =>
        All(
            "n",
            Q("Nat"),
            Imp(
                Lt(Num("7"), V("n")),
                Eq(
                    CastInt(Call("KingGrid.T", V("n"), Num("4"))),
                    Sub(
                        Add(
                            Sub(
                                Mul(Num("6"), CastInt(Call("KingGrid.T", Sub(V("n"), Num("1")), Num("4")))),
                                Mul(Num("13"), CastInt(Call("KingGrid.T", Sub(V("n"), Num("2")), Num("4"))))),
                            Mul(Num("12"), CastInt(Call("KingGrid.T", Sub(V("n"), Num("3")), Num("4"))))),
                        Mul(Num("4"), CastInt(Call("KingGrid.T", Sub(V("n"), Num("4")), Num("4"))))))));


    private static Formula V(string s) => F.Id(s);
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string s)
    {
        var parts = s.Split('_');
        Formula Word(string p) => Seq(System.Text.RegularExpressions.Regex.Matches(p, "[A-Za-z]+|[0-9]+")
            .Select(m => char.IsDigit(m.Value[0]) ? Num(m.Value) : V(m.Value)).ToArray());
        Formula result = Word(parts[^1]);
        for (var i = parts.Length - 2; i >= 0; --i)
            result = Seq(Word(parts[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Equivalence(Formula a, Formula b) => Call("Equiv", a, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Val(Formula a) => Call("Fin.val", a);
    private static Formula Value(Formula a) => Call("Subtype.val", a);
    private static Formula CastInt(Formula a) => Typed(a, Q("Int"));
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, b);
    private static Formula Subtype(string x, Formula t, Formula b) =>
        Seq(OpenBrace, V(x), Colon, Sp, t, Sp, Slash, Slash, Sp, Parenthesized(b), CloseBrace);
    private static Formula Fn(string x, Formula t, Formula b) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(x), t), Sp, Mapsto, Sp, b));
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Some(string x, Formula t, Formula b) =>
        Seq(Exists, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Unique(string x, Formula t, Formula b) =>
        Seq(Exists, Bang, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string x, Formula t, Formula b) =>
        Seq(Sum, Underscore, Grp(Seq(V(x), Colon, Sp, t)), Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));

}
