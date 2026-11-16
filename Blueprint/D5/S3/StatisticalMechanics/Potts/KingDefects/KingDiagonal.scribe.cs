using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class KingDiagonalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/KingDiagonal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: KingDiagonal"),
        Blocks(
            Node("N_D_closed", "Closed diagonal sum", Formula0(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "For at least three rows and columns, the diagonal count is the sum of two exponential boundary terms and a bilinear interior term. The displayed arithmetic is in the integers."),
            Node("N_D_two_columns", "The diagonal sum for two columns", Formula1(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "For two columns, the diagonal sum has one free binary word per defect position. The formula includes N=0."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Formula0() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                Imp(
                    Leq(Num("2"), V("N")),
                    Imp(
                        Leq(Num("2"), V("M")),
                        Eq(
                            CastInt(Call("KingDifference.N_D", V("N"), V("M"))),
                            Mul(
                                Num("6"),
                                Sub(
                                    Add(
                                        Add(
                                            Power(Typed(Num("2"), Q("Int")), Add(V("N"), Num("1"))),
                                            Power(Typed(Num("2"), Q("Int")), Add(V("M"), Num("1")))),
                                        Mul(
                                            Mul(Num("2"), Sub(CastInt(V("N")), Num("1"))),
                                            Sub(CastInt(V("M")), Num("1")))),
                                    Num("8"))))))));

    private static Formula Formula1() =>
        All(
            "N",
            Q("Nat"),
            Eq(
                Call("KingDifference.N_D", V("N"), Num("1")),
                Mul(Num("6"), Mul(V("N"), Power(Num("2"), Sub(V("N"), Num("1")))))));

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
    private static Formula CastInt(Formula a) => Call("Int.ofNat", a);
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

}
