using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class RotondoLucasCarmichaelCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/rotondo2020a006972");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rotondo's factorization conditions imply the Lucas-Carmichael divisibility criterion.",
        H("Rotondo's Lucas-Carmichael criterion"),
        Blocks(
            Paragraph(Text(
                "All variables range over the natural numbers N. The letters p, q, and r "
                    + "denote distinct odd primes, k is their product, and d is the greatest "
                    + "common divisor of p+1, q+1, and r+1. The positive factors a, b, and c "
                    + "satisfy p+1=ad, q+1=bd, and r+1=cd. A Lucas-Carmichael number is "
                    + "squarefree and composite, is greater than one, and has s+1 dividing "
                    + "k+1 for every prime divisor s of k.")),
            Node(
                "IsLucasCarmichael",
                "Lucas-Carmichael numbers",
                DefinitionFormula(),
                "A natural number k is Lucas-Carmichael when it is squarefree, composite, "
                    + "greater than one, and every prime divisor s satisfies s+1 divides k+1.",
                DescribeRole.Definition),
            Node(
                "result",
                "Rotondo's sufficient condition",
                ResultFormula(),
                "For positive a, b, c, d, p, q, r, and k satisfying the displayed product, "
                    + "prime, oddness, distinctness, factor, greatest-common-divisor, and "
                    + "divisibility hypotheses, k is Lucas-Carmichael. Distinct primality "
                    + "makes pqr squarefree and composite. Every prime divisor of pqr is one "
                    + "of p, q, and r; its successor therefore divides abcd and hence k+1.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a006972-rotondo-lucas-carmichael-sufficient-condition"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a006972-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula DefinitionFormula()
    {
        var k = F.Id("k");
        var s = F.Id("s");
        var primeDivisorCondition = Universal(["s"], ImpliesAll(
            [Call("Prime", s), Divides(s, k)],
            Divides(Add(s, D(1)), Add(k, D(1)))));
        var definition = And(
            Call("Squarefree", k),
            new Formula.Not(Call("Prime", k)),
            Less(D(1), k),
            primeDivisorCondition);
        return Disp(Universal(["k"], Iff(Call("IsLucasCarmichael", k), definition)));
    }

    private static Formula ResultFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var c = F.Id("c");
        var d = F.Id("d");
        var p = F.Id("p");
        var q = F.Id("q");
        var r = F.Id("r");
        var k = F.Id("k");
        var premises = new Formula[]
        {
            Less(D(0), a), Less(D(0), b), Less(D(0), c), Less(D(0), d),
            Less(D(0), p), Less(D(0), q), Less(D(0), r), Less(D(0), k),
            Equal(k, Multiply(Multiply(p, q), r)),
            Call("Prime", p), Call("Prime", q), Call("Prime", r),
            Call("Odd", p), Call("Odd", q), Call("Odd", r),
            NotEqual(p, q), NotEqual(p, r), NotEqual(q, r),
            Equal(Add(p, D(1)), Multiply(a, d)),
            Equal(Add(q, D(1)), Multiply(b, d)),
            Equal(Add(r, D(1)), Multiply(c, d)),
            Equal(d, Call("gcd", Add(p, D(1)),
                Call("gcd", Add(q, D(1)), Add(r, D(1))))),
            Divides(Multiply(Multiply(Multiply(a, b), c), d), Add(k, D(1))),
        };
        return Disp(Universal(
            ["a", "b", "c", "d", "p", "q", "r", "k"],
            ImpliesAll(premises, Call("IsLucasCarmichael", k))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Universal(string[] variables, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. variables.Select(variable =>
                new Formula.BoundVariable(FormulaIdentifier.Create(variable), Naturals()))],
            body);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula ImpliesAll(IReadOnlyList<Formula> premises, Formula conclusion)
    {
        var result = conclusion;
        for (int i = premises.Count - 1; i >= 0; i--)
            result = Implies(premises[i], result);
        return result;
    }
}
