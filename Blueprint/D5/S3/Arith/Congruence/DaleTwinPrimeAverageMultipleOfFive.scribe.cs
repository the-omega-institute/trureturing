using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class DaleTwinPrimeAverageMultipleOfFiveDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/gerasimov2010a177680");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twin-prime pairs centered at both 6n and 12n force n to be one or divisible by five.",
        H("Twin-Prime Averages at 6n and 12n"),
        Blocks(
            Node("IsMember", "Membership in A177680", IsMemberFormula(),
                "A positive natural number n belongs to the sequence exactly when each number "
                    + "one below and one above 6n and 12n is prime. The minus sign denotes natural "
                    + "subtraction; because n is at least one, it agrees here with ordinary subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("dale_a177680", "Dale's divisibility conjecture", TheoremFormula(),
                "Classify n by its residue modulo five. Each nonzero residue selects one of "
                    + "6n-1, 6n+1, 12n-1, and 12n+1 that is divisible by five. Its primality "
                    + "collapses that value to five: residue one gives n=1, while residues two, "
                    + "three, and four are impossible. The converse is false at n=10.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a177680-twin-prime-average-multiple-of-five"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a177680-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula IsMemberFormula()
    {
        var n = F.Id("n");
        var conditions = And(
            LessOrEqual(D(1), n),
            And(
                Prime(Subtract(Multiply(D(6), n), D(1))),
                And(
                    Prime(Add(Multiply(D(6), n), D(1))),
                    And(
                        Prime(Subtract(Multiply(D(1, 2), n), D(1))),
                        Prime(Add(Multiply(D(1, 2), n), D(1)))))));
        return Disp(ForAll([Bound("n")],
            Iff(Call("IsMember", n), Parenthesized(conditions))));
    }

    private static Formula TheoremFormula()
    {
        var n = F.Id("n");
        var conclusion = Or(Equal(n, D(1)), Divides(D(5), n));
        return Disp(ForAll([Bound("n")], Implies(Call("IsMember", n), conclusion)));
    }

    private static Formula.BoundVariable Bound(string name) => new Formula.BoundVariable(
        FormulaIdentifier.Create(name), Naturals());

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [.. variables],
        body);

    private static Formula Naturals() => new Formula.LatexGroup([Mathbb, Sp, F.Id("N")]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Prime(Formula value) => Call("Prime", value);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
