using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class KingClosedFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/KingClosedForm.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: KingClosedForm"),
        Blocks(
            Node("closed_form", "The canonical count for both side lengths at least four", Formula0(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The two horizontal-orientation sums and the diagonal sum give the formula after removing colour labels. Every natural count and both dimensions in the polynomial are explicitly cast to integers."),
            Node("width_two", "The width-two closed form", Formula1(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The formula holds for every height at least two; subtraction in the exponent is natural subtraction."),
            Node("width_three", "The width-three closed form", Formula2(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The heights two and three are included. The general formula follows from the orientation sums."),
            Node("diagonal_closed", "Square arrays", Formula3(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The square case includes side length three and otherwise specializes the two-dimensional closed form."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Formula0() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                Imp(
                    Leq(Num("4"), V("n")),
                    Imp(
                        Leq(Num("4"), V("k")),
                        Eq(
                            Mul(Num("4"), CastInt(Call("KingGrid.T", V("n"), V("k")))),
                            Sub(
                                Sub(
                                    Sub(
                                        Add(
                                            Add(
                                                Mul(
                                                    Add(
                                                        Add(
                                                            Sub(
                                                                Mul(CastInt(V("n")), CastInt(V("k"))),
                                                                CastInt(V("n"))),
                                                            Mul(Num("6"), CastInt(V("k")))),
                                                        Num("12")),
                                                    Power(Typed(Num("2"), Q("Int")), V("n"))),
                                                Mul(
                                                    Add(
                                                        Add(
                                                            Sub(
                                                                Mul(CastInt(V("n")), CastInt(V("k"))),
                                                                CastInt(V("k"))),
                                                            Mul(Num("6"), CastInt(V("n")))),
                                                        Num("12")),
                                                    Power(Typed(Num("2"), Q("Int")), V("k")))),
                                            Mul(Mul(Num("16"), CastInt(V("n"))), CastInt(V("k")))),
                                        Mul(Num("64"), CastInt(V("n")))),
                                    Mul(Num("64"), CastInt(V("k")))),
                                Num("32")))))));

    private static Formula Formula1() =>
        All(
            "n",
            Q("Nat"),
            Imp(
                Leq(Num("2"), V("n")),
                Eq(
                    CastInt(Call("KingGrid.T", V("n"), Num("2"))),
                    Mul(
                        Sub(Mul(Num("7"), CastInt(V("n"))), Num("8")),
                        Power(Typed(Num("2"), Q("Int")), Sub(V("n"), Num("2")))))));

    private static Formula Formula2() =>
        All(
            "n",
            Q("Nat"),
            Imp(
                Leq(Num("2"), V("n")),
                Eq(
                    Mul(Num("4"), CastInt(Call("KingGrid.T", V("n"), Num("3")))),
                    Sub(
                        Add(
                            Mul(
                                Add(Mul(Num("3"), CastInt(V("n"))), Num("27")),
                                Power(Typed(Num("2"), Q("Int")), V("n"))),
                            Mul(Num("44"), CastInt(V("n")))),
                        Num("116")))));

    private static Formula Formula3() =>
        All(
            "n",
            Q("Nat"),
            Imp(
                Leq(Num("3"), V("n")),
                Eq(
                    Mul(Num("2"), CastInt(Call("KingGrid.T", V("n"), V("n")))),
                    Sub(
                        Sub(
                            Add(
                                Mul(
                                    Add(
                                        Add(
                                            Power(CastInt(V("n")), Num("2")),
                                            Mul(Num("5"), CastInt(V("n")))),
                                        Num("12")),
                                    Power(Typed(Num("2"), Q("Int")), V("n"))),
                                Mul(Num("8"), Power(CastInt(V("n")), Num("2")))),
                            Mul(Num("64"), CastInt(V("n")))),
                        Num("16")))));

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
