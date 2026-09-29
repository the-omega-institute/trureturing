using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Billiards;

internal sealed class CollidingBlocksRecordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Constants/Billiards/CollidingBlocksRecords.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Dynamics/kagey2020a331859");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the number a(n) of elastic collisions between a block of mass n, a block of mass 1 and a wall, every n at which a(n) differs from floor(pi sqrt(n)) is a position of a record of a (OEIS A331859, conjecture of Kagey).",
        H("Colliding blocks: where the collision count leaves floor(pi sqrt n), it sets a record"),
        Blocks(
            Node("a", "The collision count of the colliding blocks", CountFormula(),
                "OEIS A331859, COMMENTS: \"Suppose there is a block A of mass n sliding left toward a stationary block B of mass 1, to the left of which is a wall. Assuming the sliding is frictionless and the collisions are elastic, a(n) is the number of collisions between A and B plus the number of collisions between B and the wall.\" The definition is the entry's FORMULA line \"a(n) = ceiling(Pi/arctan(sqrt(1/n))) - 1.\", Galperin's count of these collisions, for n at least one.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture of OEIS A331859", ClaimDefinitionFormula(),
                "OEIS A331859, COMMENTS: \"Conjecture: The values of n for which a(n) != A121854(n) is a subset of A331903.\" Here A121854(n) = floor(Pi*(sqrt(n))), and A331903, the positions of records in A331859, consists of the n at least one with a(k) < a(n) for all k with 1 <= k < n.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Every exceptional n is a record position", ClaimFormula(),
                "Write t(m) = arctan(sqrt(1/m)), so that a(m) is the largest integer strictly below pi/t(m). Since t decreases, a is nondecreasing. Since arctan y < y for y > 0 (from y < tan y), t(n) < 1/sqrt(n), so pi/t(n) > pi sqrt(n) and a(n) >= floor(pi sqrt(n)). For n >= 2, sin t(n - 1) = 1/sqrt(n) and sin t < t, so t(n - 1) > 1/sqrt(n) and pi/t(n - 1) < pi sqrt(n). If a(n) differs from floor(pi sqrt(n)), then a(n) >= floor(pi sqrt(n)) + 1 > pi sqrt(n) > pi/t(n - 1) > a(n - 1) >= a(k) for every k < n, so n is a record position; for n = 1 there is no k to compare.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kagey-2020-a331859-colliding-blocks-records"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("colliding-blocks-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));

    private static Formula CountFormula()
    {
        Formula n = F.Id("n");
        Formula angle = Call("arctan", Root(new Formula.Fraction(D(1), n)));
        Formula value = Subtract(Call("ceil", new Formula.Fraction(Pi, angle)), D(1));
        return Disp(All("n", Naturals(), Equal(Call("a", n), value)));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula exceptional = NotEqual(Call("a", n), new Formula.Floor(Mul(Pi, Root(n))));
        Formula record = All("k", Naturals(), Implies(AtMost(D(1), k),
            Implies(Less(k, n), Less(Call("a", k), Call("a", n)))));
        return All("n", Naturals(), Implies(AtMost(D(1), n), Implies(exceptional, record)));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimFormula() => Disp(F.Id("claim"));
}
