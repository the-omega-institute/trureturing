using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class FallingFactorialMomentBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/FallingFactorialMomentBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/malik2020entropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every integer k >= 1 and every integer 0 <= n <= k, n^2/k (1/k)^n k!/(k - n)! <= 1, that is, n^2 k(k - 1)...(k - n + 1) <= k^(n + 1). This is the conjecture stated after eq. (003.21) by T. A. Malik and R. Lopez-Mobilia (arXiv:2004.07168), who checked it numerically; they use it for the corollary h(k) in (1/k, k), which is not formalized here.",
        H("A bound on n^2 times a falling factorial"),
        Blocks(
            Node("claim", "The conjecture", ClaimFormula(),
                "The conjecture after eq. (003.21) of the paper, written with k for k'. Here k - n is subtraction of natural numbers, exact since n <= k, and the factorials are read in the real numbers.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Since k!/(k - n)! = k(k - 1)...(k - n + 1), the claim is n^2 k(k - 1)...(k - n + 1) <= k^(n + 1). For n <= 3 this is direct: n = 2 reads 4(k - 1) <= k^2, and n = 3 reads 9 k(k - 1)(k - 2) <= k^4, which follows from k^4 - 9 k(k - 1)(k - 2) = k((k - 3)^3 + 9). For n >= 4, k(k - 1)...(k - n + 1) = k^n times the product of 1 - i/k over i < n, and 1 - x <= e^(-x) bounds this product by e^(-u) with u = n(n - 1)/(2k). Since u e^(-u) <= e^(-1) < 3/8, (n - 1) n^2 e^(-u) = 2 n k u e^(-u) <= (3/4) n k <= (n - 1) k, so n^2 e^(-u) <= k and the claim follows.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("fallingmoment-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Div(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Factorial(Formula value) => Seq(value, Bang);

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n");
        Formula term = Mul(Mul(Div(Pow(n, D(2)), k), Pow(Parenthesized(Div(D(1), k)), n)),
            Parenthesized(Div(Factorial(k), Factorial(Parenthesized(Sub(k, n))))));
        Formula bound = Rel(term, FormulaRelationOperator.LessThanOrEqual, D(1));
        Formula body = Implies(Rel(D(1), FormulaRelationOperator.LessThanOrEqual, k),
            All("n", Nats(), Implies(Rel(n, FormulaRelationOperator.LessThanOrEqual, k), bound)));
        return Disp(Iff(F.Id("claim"), All("k", Nats(), body)));
    }
}
