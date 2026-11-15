using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class HardinA229578Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229578.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: HardinA229578"),
        Blocks(
            Node("result", "The seven column recurrences", Formula0(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The seven conjuncts concern columns one through seven, in that order. Each retains its own height threshold. The first column follows from the path formula; the remaining columns follow from their respective fixed-width formulas."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229578"), ResolutionKind.Proved));

    private static Formula Formula0() =>
        And(
            All(
                "n",
                Q("Nat"),
                Imp(
                    Lt(Num("6"), V("n")),
                    Eq(
                        CastInt(Call("KingGrid.T", V("n"), Num("1"))),
                        Sub(
                            Add(
                                Sub(
                                    Mul(
                                        Num("8"),
                                        CastInt(Call("KingGrid.T", Sub(V("n"), Num("1")), Num("1")))),
                                    Mul(
                                        Num("22"),
                                        CastInt(Call("KingGrid.T", Sub(V("n"), Num("2")), Num("1"))))),
                                Mul(Num("24"), CastInt(Call("KingGrid.T", Sub(V("n"), Num("3")), Num("1"))))),
                            Mul(Num("9"), CastInt(Call("KingGrid.T", Sub(V("n"), Num("4")), Num("1")))))))),
            And(
                All(
                    "n",
                    Q("Nat"),
                    Imp(
                        Lt(Num("3"), V("n")),
                        Eq(
                            CastInt(Call("KingGrid.T", V("n"), Num("2"))),
                            Sub(
                                Mul(Num("4"), CastInt(Call("KingGrid.T", Sub(V("n"), Num("1")), Num("2")))),
                                Mul(Num("4"), CastInt(Call("KingGrid.T", Sub(V("n"), Num("2")), Num("2")))))))),
                And(
                    All(
                        "n",
                        Q("Nat"),
                        Imp(
                            Lt(Num("5"), V("n")),
                            Eq(
                                CastInt(Call("KingGrid.T", V("n"), Num("3"))),
                                Sub(
                                    Add(
                                        Sub(
                                            Mul(
                                                Num("6"),
                                                CastInt(Call("KingGrid.T", Sub(V("n"), Num("1")), Num("3")))),
                                            Mul(
                                                Num("13"),
                                                CastInt(Call("KingGrid.T", Sub(V("n"), Num("2")), Num("3"))))),
                                        Mul(
                                            Num("12"),
                                            CastInt(Call("KingGrid.T", Sub(V("n"), Num("3")), Num("3"))))),
                                    Mul(
                                        Num("4"),
                                        CastInt(Call("KingGrid.T", Sub(V("n"), Num("4")), Num("3")))))))),
                    And(
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
                                                Mul(
                                                    Num("6"),
                                                    CastInt(
                                                        Call("KingGrid.T", Sub(V("n"), Num("1")), Num("4")))),
                                                Mul(
                                                    Num("13"),
                                                    CastInt(
                                                        Call("KingGrid.T", Sub(V("n"), Num("2")), Num("4"))))),
                                            Mul(
                                                Num("12"),
                                                CastInt(Call("KingGrid.T", Sub(V("n"), Num("3")), Num("4"))))),
                                        Mul(
                                            Num("4"),
                                            CastInt(Call("KingGrid.T", Sub(V("n"), Num("4")), Num("4")))))))),
                        And(
                            All(
                                "n",
                                Q("Nat"),
                                Imp(
                                    Lt(Num("7"), V("n")),
                                    Eq(
                                        CastInt(Call("KingGrid.T", V("n"), Num("5"))),
                                        Sub(
                                            Add(
                                                Sub(
                                                    Mul(
                                                        Num("6"),
                                                        CastInt(
                                                            Call(
                                                                "KingGrid.T",
                                                                Sub(V("n"), Num("1")),
                                                                Num("5")))),
                                                    Mul(
                                                        Num("13"),
                                                        CastInt(
                                                            Call(
                                                                "KingGrid.T",
                                                                Sub(V("n"), Num("2")),
                                                                Num("5"))))),
                                                Mul(
                                                    Num("12"),
                                                    CastInt(
                                                        Call("KingGrid.T", Sub(V("n"), Num("3")), Num("5"))))),
                                            Mul(
                                                Num("4"),
                                                CastInt(Call("KingGrid.T", Sub(V("n"), Num("4")), Num("5")))))))),
                            And(
                                All(
                                    "n",
                                    Q("Nat"),
                                    Imp(
                                        Lt(Num("7"), V("n")),
                                        Eq(
                                            CastInt(Call("KingGrid.T", V("n"), Num("6"))),
                                            Sub(
                                                Add(
                                                    Sub(
                                                        Mul(
                                                            Num("6"),
                                                            CastInt(
                                                                Call(
                                                                    "KingGrid.T",
                                                                    Sub(V("n"), Num("1")),
                                                                    Num("6")))),
                                                        Mul(
                                                            Num("13"),
                                                            CastInt(
                                                                Call(
                                                                    "KingGrid.T",
                                                                    Sub(V("n"), Num("2")),
                                                                    Num("6"))))),
                                                    Mul(
                                                        Num("12"),
                                                        CastInt(
                                                            Call(
                                                                "KingGrid.T",
                                                                Sub(V("n"), Num("3")),
                                                                Num("6"))))),
                                                Mul(
                                                    Num("4"),
                                                    CastInt(
                                                        Call("KingGrid.T", Sub(V("n"), Num("4")), Num("6")))))))),
                                All(
                                    "n",
                                    Q("Nat"),
                                    Imp(
                                        Lt(Num("7"), V("n")),
                                        Eq(
                                            CastInt(Call("KingGrid.T", V("n"), Num("7"))),
                                            Sub(
                                                Add(
                                                    Sub(
                                                        Mul(
                                                            Num("6"),
                                                            CastInt(
                                                                Call(
                                                                    "KingGrid.T",
                                                                    Sub(V("n"), Num("1")),
                                                                    Num("7")))),
                                                        Mul(
                                                            Num("13"),
                                                            CastInt(
                                                                Call(
                                                                    "KingGrid.T",
                                                                    Sub(V("n"), Num("2")),
                                                                    Num("7"))))),
                                                    Mul(
                                                        Num("12"),
                                                        CastInt(
                                                            Call(
                                                                "KingGrid.T",
                                                                Sub(V("n"), Num("3")),
                                                                Num("7"))))),
                                                Mul(
                                                    Num("4"),
                                                    CastInt(
                                                        Call("KingGrid.T", Sub(V("n"), Num("4")), Num("7"))))))))))))));

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
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

}
