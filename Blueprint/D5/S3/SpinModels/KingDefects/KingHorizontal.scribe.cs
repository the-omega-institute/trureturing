using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpinModels.KingDefects;

internal sealed class KingHorizontalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/SpinModels/KingDefects/KingHorizontal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: KingHorizontal"),
        Blocks(
            Node("horizontal_two_rows", "Horizontal defects in two rows", Formula0(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The natural count is six times the number of positions times a binary-word count."),
            Node("horizontal_two_columns", "Horizontal defects in two columns", Formula1(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The natural formula separates the boundary rows from the interior rows."),
            Node("horizontal_three_rows", "Horizontal defects in three rows", Formula2(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The additive form keeps every operation in the natural numbers."),
            Node("horizontal_sum", "The general horizontal orientation sum", Formula3(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The rectangle has t+4 rows and q+3 columns. Summing the boundary and interior defect counts yields this identity in natural arithmetic."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Formula0() =>
        All(
            "M",
            Q("Nat"),
            Eq(
                Call("KingDifference.N_H", Num("1"), V("M")),
                Mul(Num("6"), Mul(V("M"), Power(Num("2"), V("M"))))));

    private static Formula Formula1() =>
        All(
            "p",
            Q("Nat"),
            Eq(
                Call("KingDifference.N_H", Add(V("p"), Num("1")), Num("1")),
                Mul(Num("6"), Mul(Add(Mul(Num("3"), V("p")), Num("2")), Power(Num("2"), V("p"))))));

    private static Formula Formula2() =>
        All(
            "q",
            Q("Nat"),
            Eq(
                Add(Call("KingDifference.N_H", Num("2"), Add(V("q"), Num("1"))), Num("54")),
                Mul(
                    Num("6"),
                    Add(
                        Mul(Add(V("q"), Num("13")), Power(Num("2"), V("q"))),
                        Mul(Num("3"), Add(V("q"), Num("2")))))));

    private static Formula Formula3() =>
        All(
            "t",
            Q("Nat"),
            All(
                "q",
                Q("Nat"),
                Eq(
                    Add(
                        Call("KingDifference.N_H", Add(V("t"), Num("3")), Add(V("q"), Num("2"))),
                        Mul(Num("6"), Add(Mul(Num("8"), Add(V("t"), Num("4"))), Num("4")))),
                    Mul(
                        Num("6"),
                        Add(
                            Mul(
                                Add(Mul(Add(V("t"), Num("4")), Add(V("q"), Num("2"))), Num("8")),
                                Power(Num("2"), Add(V("t"), Num("2")))),
                            Mul(
                                Add(Mul(Num("3"), V("t")), Num("10")),
                                Power(Num("2"), Add(V("q"), Num("2")))))))));


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
