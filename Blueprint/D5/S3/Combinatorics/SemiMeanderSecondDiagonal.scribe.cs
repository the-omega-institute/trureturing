using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class SemiMeanderSecondDiagonalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SemiMeanderSecondDiagonal.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/hogan2026a400429");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connected semi-meanders with n crossings and winding n minus four have the second-diagonal count for every n at least four.",
        H("The Second Semi-Meander Diagonal"),
        Blocks(
            Describe.Lean(DescribeId.Create("upper-matching"),
                DeclarationHandle.Create(Prefix + "UpperMatching"),
                H("Noncrossing upper arches"), StatementSource.FromAuthor(UpperMatchingFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Endpoints are numbered from zero to 2n minus one. "
                    + "An upper matching is a fixed-point-free involution M: each endpoint "
                    + "has one distinct partner, and no two upper arches have alternating "
                    + "endpoints a < b < M(a) < M(b). The fixed lower matching is the "
                    + "rainbow r(x) = 2n - 1 - x."))), DescribeRole.Definition),
            Describe.Remark(DescribeId.Create("midpoint-winding"),
                H("Midpoint winding"), WindingFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("L_n embeds Fin n into Fin(2n) without changing the "
                    + "endpoint value. The winding counts left-half endpoints whose upper "
                    + "partner lies in the right half. Each upper arch crossing the midpoint "
                    + "contributes exactly once.")))),
            Describe.Remark(DescribeId.Create("one-loop"),
                H("One loop with the lower rainbow"), OneLoopFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The step relation R_M joins x to y when either "
                    + "M(x) = y or r(x) = y, with r(x) = 2n - 1 - x. Its reflexive "
                    + "transitive closure connects every ordered pair of endpoints exactly "
                    + "when the union of upper arches and the fixed lower rainbow is one loop.")))),
            Describe.Lean(DescribeId.Create("second-diagonal-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Exact second-diagonal count"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every n at least four, count exactly the "
                    + "noncrossing upper matchings whose midpoint winding is n minus four "
                    + "and whose union with the lower rainbow is one loop. The second "
                    + "diagonal of OEIS A400429 is this set: its source index "
                    + "k = floor(n/2) - 1 gives winding n - 4. At n = 4 the count is two. "
                    + "Di Francesco, Golinelli and Guitter predicted this same polynomial "
                    + "from the resummation in Appendix D (1996); the count here is an "
                    + "independent exact proof for the stated model and full range."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a400429-semi-meander-second-diagonal"),
                    ResolutionKind.Proved))),
        []));

    private static Formula N() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula E(Formula n) => Call("Fin", Multiply(D(2), n));
    private static Formula App(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Eq(Formula x, Formula y) => Equal(x, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Leq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Neq(Formula x, Formula y) => NotEqual(x, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Or(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Or, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Sub(Formula x, Formula y) => Subtract(x, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Mod(Formula x, Formula y) => new Formula.Modulo(x, y);
    private static Formula Card(Formula x) => new Formula.Absolute(x);
    private static Formula Set(Formula variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, variable, Sp, InMacro, Sp, domain, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula UpperMatchingFormula()
    {
        var n = F.Id("n"); var x = F.Id("x"); var a = F.Id("a");
        var b = F.Id("b"); var m = F.Id("M"); var e = E(n);
        var involution = All("x", e, And(Eq(App(m, App(m, x)), x), Neq(App(m, x), x)));
        var crossing = And(Lt(a, b), And(Lt(b, App(m, a)), Lt(App(m, a), App(m, b))));
        var noncrossing = All("a", e, All("b", e, new Formula.Not(crossing)));
        return Disp(Eq(new Formula.Subscript(F.Id("U"), n),
            Set(m, new Formula.TypeArrow(e, e), And(involution, noncrossing))));
    }

    private static Formula WindingFormula()
    {
        var n = F.Id("n"); var x = F.Id("x"); var m = F.Id("M");
        var left = new Formula.Subscript(F.Id("L"), n);
        var leftEndpoint = App(left, x);
        var leftType = new Formula.TypeArrow(Call("Fin", n), E(n));
        return Disp(Seq(
            left, Colon, Sp, leftType, Comma, Sp,
            All("x", Call("Fin", n), Eq(Call("val", leftEndpoint), Call("val", x))),
            Comma, Sp,
            Eq(Call("winding", m), Card(Set(x, Call("Fin", n),
                Leq(n, Call("val", App(m, leftEndpoint))))))));
    }

    private static Formula OneLoopFormula()
    {
        var n = F.Id("n"); var x = F.Id("x"); var y = F.Id("y");
        var u = F.Id("u"); var v = F.Id("v"); var m = F.Id("M");
        var relationName = new Formula.Subscript(F.Id("R"), m);
        var rainbow = Sub(Sub(Multiply(D(2), n), D(1)), Call("val", u));
        var edge = Or(Eq(App(m, u), v), Eq(rainbow, Call("val", v)));
        var relation = All("u", E(n), All("v", E(n),
            Iff(new Formula.Apply(relationName, [u, v]), edge)));
        var connected = All("x", E(n), All("y", E(n),
            Call("RTC", relationName, x, y)));
        return Disp(Seq(relation, Comma, Sp, Sp,
            Iff(Call("oneLoop", m), connected)));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n"); var m = F.Id("M");
        var matching = Set(m, new Formula.Subscript(F.Id("U"), n),
            And(Eq(Call("winding", m), Sub(n, D(4))), Call("oneLoop", m)));
        var numerator = Sub(Add(Add(Pow(n, D(2)), Multiply(D(2), n)),
            Mod(n, D(2))), D(2, 0));
        return Disp(All("n", N(), Imp(Leq(D(4), n),
            Eq(Card(matching), new Formula.Fraction(numerator, D(2))))));
    }
}
