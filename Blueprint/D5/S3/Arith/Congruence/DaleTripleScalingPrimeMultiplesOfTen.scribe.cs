using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class DaleTripleScalingPrimeMultiplesOfTenDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/cami2015a112041");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four prime values at successive powers-of-three scalings force k to be four or divisible by ten.",
        H("Dale's A112041 Prime-Scaling Conjecture"),
        Blocks(
            Node("claim", "Dale's divisibility conjecture", ClaimFormula(),
                "For every positive natural k, if k+1, 3k+1, 9k+1, and 27k+1 are "
                    + "all prime, then k is four or divisible by ten.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The prime-scaling theorem", ResultFormula(),
                "Parity first forces k to be even: an odd k would make the prime k+1 "
                    + "equal to two, after which 3k+1 is composite. A split into residue "
                    + "classes modulo five then makes one of 9k+1, 27k+1, or 3k+1 a "
                    + "proper multiple of five, except when k is congruent to four and "
                    + "the prime k+1 equals five. The remaining residue class is divisible "
                    + "by both two and five.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a112041-dale-triple-scaling-prime-multiples-of-ten"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("a112041-" + name),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula ClaimFormula()
    {
        var k = F.Id("k");
        var primes = And(
            Prime(Add(k, D(1))),
            And(
                Prime(Add(Multiply(D(3), k), D(1))),
                And(
                    Prime(Add(Multiply(D(9), k), D(1))),
                    Prime(Add(Multiply(D(2, 7), k), D(1))))));
        var conclusion = Or(Equal(k, D(4)), Divides(D(1, 0), k));
        return Disp(ForAll([Bound("k")],
            Implies(
                Greater(k, D(0)),
                Implies(Parenthesized(primes), Parenthesized(conclusion)))));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula.BoundVariable Bound(string name) => new(
        FormulaIdentifier.Create(name), Naturals());

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Naturals() =>
        new Formula.LatexGroup([Mathbb, Sp, F.Id("N")]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Prime(Formula value) => Call("Prime", value);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
