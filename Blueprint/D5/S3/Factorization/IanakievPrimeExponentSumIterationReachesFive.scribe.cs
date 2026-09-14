using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class IanakievPrimeExponentSumIterationReachesFiveDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/IanakievPrimeExponentSumIterationReachesFive.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ianakiev2014a008474");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every prime-exponent sum orbit starting above four reaches five.",
        H("Ianakiev's A008474 Iteration Conjecture"),
        Blocks(
            Node("F", "The prime-exponent sum", DefinitionFormula(),
                "For every natural n, F(n) sums p plus the exponent of p over the "
                    + "distinct prime divisors of n. The empty prime-factor sets at zero "
                    + "and one give F(0)=F(1)=0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ianakiev_a008474", "Every orbit above four reaches five", TheoremFormula(),
                "For every natural m greater than four, some finite iterate of F equals five. "
                    + "The displayed superscript [t] denotes Function.iterate (Nat.iterate). "
                    + "Composite inputs descend in one step and sufficiently large prime inputs "
                    + "descend in two steps. The remaining values enter the cycle "
                    + "5 -> 6 -> 7 -> 8 -> 5. Since four is fixed, the lower bound is sharp. "
                    + "No generating-function identity is asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a008474-prime-exponent-sum-iteration-reaches-five"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a008474-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula DefinitionFormula()
    {
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula index = new Formula.Relation(
            p, FormulaRelationOperator.MemberOf, Call("primeFactors", n));
        Formula summand = Parenthesized(Add(p, Call("factorization", n, p)));
        Formula sum = Seq(new Formula.Subscript(Sum, index), Sp, summand);
        return Disp(ForAll([Bound("n")], Equal(Call("F", n), sum)));
    }

    private static Formula TheoremFormula()
    {
        Formula m = F.Id("m");
        Formula t = F.Id("t");
        Formula iteratedF = new Formula.Power(
            F.Id("F"), Seq(OpenBracket, t, CloseBracket));
        Formula iterateAtM = new Formula.Apply(iteratedF, [m]);
        return Disp(ForAll([Bound("m")],
            Implies(Less(D(4), m),
                Exists([Bound("t")], Equal(iterateAtM, D(5))))));
    }

    private static Formula.BoundVariable Bound(string name) => new(
        FormulaIdentifier.Create(name), Naturals());

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Naturals() => new Formula.LatexGroup([Mathbb, Sp, F.Id("N")]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
}
