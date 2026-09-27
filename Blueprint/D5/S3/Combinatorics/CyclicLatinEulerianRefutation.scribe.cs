using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class CyclicLatinEulerianRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/CyclicLatinEulerianRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/mirzavaziri2026cyclic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The column-ascent counts of cyclic Latin squares change only when an endpoint "
            + "symbol wraps, which refutes full permutation symmetry of the ascent vector.",
        H("Cyclic Latin Eulerian Numbers Are Not Fully Symmetric"),
        Blocks(
            Node("cyclic-square", "Row-reordered cyclic square", "cyclicSquare",
                CyclicSquareFormula(),
                "The entry in row i and column c is the value of the row permutation at i, "
                    + "shifted by c in Fin n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cyclic-latin-eulerian", "Cyclic Latin Eulerian number",
                "cyclicLatinEulerian", CyclicLatinEulerianFormula(),
                "Count the row permutations whose column-ascent vector equals k at every "
                    + "column. Column ascents are counted from the first row to the last.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("full-symmetry-claim", "Full permutation symmetry", "claim",
                ClaimFormula(),
                "The asserted equality compares the count for k with the count for k "
                    + "after any permutation of its column coordinates, at every order.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("shift-step", "One-column shift identity", "shift_step",
                ShiftStepFormula(),
                "For order at least two, shifting the column by one changes its ascent "
                    + "count only through the wrapping symbol in the first and last rows. "
                    + "The endpoint indicators balance the two column counts.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("no-three-changes", "Three consecutive shifts cannot all change",
                "no_three_changes", NoThreeChangesFormula(),
                "At order at least four, among the first three successive column pairs, "
                    + "at least one pair has equal ascent counts. Distinct wrapping symbols "
                    + "cannot all occupy the two endpoint rows.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("not-fully-symmetric", "Failure at every order at least four",
                "not_fully_symmetric", NotFullySymmetricFormula(),
                "Exchange the last two values of the identity row permutation, then "
                    + "exchange the second and third coordinates of its ascent vector. "
                    + "The original vector is attained, while the exchanged vector would "
                    + "require three consecutive changes and is unattained.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("full-symmetry-refuted", "Full symmetry is false", "result",
                ResultFormula(),
                "The asserted equality fails already at order four, and the preceding "
                    + "construction supplies a failure at every larger order.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mirzavaziri-yaqubi-cyclic-full-symmetry-refutation"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Nat() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Fin(Formula n) => Call("Fin", n);

    private static Formula Perm(Formula n) => Call("EquivPerm", Fin(n));

    private static Formula Vector(Formula n) =>
        new Formula.TypeArrow(Fin(n), Nat());

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),
            domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name),
            domain, body);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Compose(Formula k, Formula sigma) =>
        Seq(k, Sp, Circ, Sp, sigma);

    private static Formula FinIndex(Formula n, Formula index) =>
        Call("fin", index, n);

    private static Formula Column(Formula n, Formula pi, Formula index) =>
        Call("colAscents", n, Call("cyclicSquare", n, pi), FinIndex(n, index));

    private static Formula Indicator(Formula condition) =>
        Call("if", condition, D(1), D(0));

    private static Formula CyclicSquareFormula()
    {
        var n = F.Id("n"); var pi = F.Id("pi");
        var i = F.Id("i"); var c = F.Id("c");
        return Disp(All("n", Nat(), All("pi", Perm(n), All("i", Fin(n),
            All("c", Fin(n), Eq(Call("cyclicSquare", n, pi, i, c),
                Add(Call("pi", i), c)))))));
    }

    private static Formula CyclicLatinEulerianFormula()
    {
        var n = F.Id("n"); var k = F.Id("k");
        var pi = F.Id("pi"); var j = F.Id("j");
        var condition = All("j", Fin(n),
            Eq(Call("colAscents", n, Call("cyclicSquare", n, pi), j), Call("k", j)));
        var set = Seq(OpenBrace, Sp, pi, Sp, InMacro, Sp, Perm(n), Sp, Bar, Sp,
            condition, CloseBrace, Sp);
        return Disp(All("n", Nat(), All("k", Vector(n),
            Eq(Call("cyclicLatinEulerian", n, k), Call("card", set)))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var sigma = F.Id("sigma");
        var equality = Eq(Call("cyclicLatinEulerian", n, Compose(k, sigma)),
            Call("cyclicLatinEulerian", n, k));
        return Disp(Iff(F.Id("claim"), All("n", Nat(),
            All("k", Vector(n), All("sigma", Perm(n), equality)))));
    }

    private static Formula ShiftStepFormula()
    {
        var n = F.Id("n"); var pi = F.Id("pi"); var c = F.Id("c");
        var one = FinIndex(n, D(1));
        var first = FinIndex(n, D(0));
        var last = FinIndex(n, Sub(n, D(1)));
        var wrapping = Sub(n, D(1));
        var lastIndicator = Indicator(Eq(Call("val", Add(Call("pi", last), c)), wrapping));
        var firstIndicator = Indicator(Eq(Call("val", Add(Call("pi", first), c)), wrapping));
        var identity = Eq(
            Add(Call("colAscents", n, Call("cyclicSquare", n, pi), Add(c, one)),
                lastIndicator),
            Add(Call("colAscents", n, Call("cyclicSquare", n, pi), c),
                firstIndicator));
        return Disp(All("n", Nat(), All("pi", Perm(n), All("c", Fin(n),
            Imp(Le(D(2), n), identity)))));
    }

    private static Formula NoThreeChangesFormula()
    {
        var n = F.Id("n"); var pi = F.Id("pi");
        var alternatives = Or(Eq(Column(n, pi, D(0)), Column(n, pi, D(1))),
            Or(Eq(Column(n, pi, D(1)), Column(n, pi, D(2))),
                Eq(Column(n, pi, D(2)), Column(n, pi, D(3)))));
        return Disp(All("n", Nat(), All("pi", Perm(n),
            Imp(Le(D(4), n), alternatives))));
    }

    private static Formula NotFullySymmetricFormula()
    {
        var n = F.Id("n"); var k = F.Id("k"); var sigma = F.Id("sigma");
        var failure = Ne(Call("cyclicLatinEulerian", n, Compose(k, sigma)),
            Call("cyclicLatinEulerian", n, k));
        return Disp(All("n", Nat(), Imp(Le(D(4), n),
            Exists("k", Vector(n), Exists("sigma", Perm(n), failure)))));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));
}
