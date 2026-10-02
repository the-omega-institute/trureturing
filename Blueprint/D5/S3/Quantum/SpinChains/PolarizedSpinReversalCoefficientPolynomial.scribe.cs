using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class PolarizedSpinReversalCoefficientPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/PolarizedSpinReversalCoefficientPolynomial.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/basumallick2015dn");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For all natural numbers N and k <= N, the coefficient f_{N,k}(q) = (q^{N-k} + q^k)/(1 + q^N) [N, k]_{q^2} in the partition function of the D_N-type Polychronakos-Frahm spin chain with polarized spin reversal operators is a polynomial in q. This proves the conjecture of B. Basu-Mallick, C. Datta, F. Finkel and A. Gonzalez-Lopez (arXiv:1503.08231).",
        H("The coefficients f_{N,k}(q) are polynomials"),
        Blocks(
            Node("poch", "The q-Pochhammer products", PochFormula(),
                "Here q is the indeterminate of the field Q(q) of rational functions (RatFunc.X in Lean), and (q^2)_j is the product of 1 - q^{2i} over i = 1, ..., j, as in Eq. (m40) of the paper.",
                "qPoch", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("binom", "The q-binomial coefficients", BinomFormula(),
                "The q-binomial coefficient [N, k]_{q^2} is (q^2)_N / ((q^2)_k (q^2)_{N-k}) in Q(q); in Lean the subtraction N - k is natural-number subtraction, and the claim uses only k <= N.",
                "qBinom", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coeff", "The coefficients", CoeffFormula(),
                "The coefficient f_{N,k}(q) of Eq. (m39) of the paper multiplies [N, k]_{q^2} by (q^{N-k} + q^k)/(1 + q^N).",
                "coeffF", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "For every N and every k <= N there is a polynomial p with rational coefficients whose image in Q(q) is f_{N,k}(q). The paper conjectures that f_{N,k}(q) is a polynomial in q.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Polynomiality", Disp(F.Id("claim")),
                "Write B(a, b) = [a + b, a]_{q^2}. Since (q^2)_{j+1} = (q^2)_j (1 - q^{2(j+1)}) and (1 - q^{2a}) + q^{2a}(1 - q^{2b}) = 1 - q^{2(a+b)}, the q-Pascal rules B(a, b) = B(a - 1, b) + q^{2a} B(a, b - 1) and B(a, b) = q^{2b} B(a - 1, b) + B(a, b - 1) hold for a, b >= 1, so B(a, b) is a polynomial by induction on a + b, starting from B(a, 0) = B(0, b) = 1. Multiplying the first rule by q^b and the second by q^a and adding gives (q^b + q^a) B(a, b) = (1 + q^{a+b})(q^b B(a - 1, b) + q^a B(a, b - 1)). Hence f_{N,k} = q^{N-k} [N - 1, k - 1]_{q^2} + q^k [N - 1, k]_{q^2} for 1 <= k <= N - 1, and f_{N,0} = f_{N,N} = 1.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("basu-mallick-2015-dn-psro-coefficient-polynomiality"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("dnpsro-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Plus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Minus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q() => F.Id("q");

    private static Formula PochFormula()
    {
        Formula j = F.Id("j"), i = F.Id("i");
        Formula product = Seq(F.Prod, Underscore, Grp(i, Eq, D(1)), Caret, Grp(j), Sp,
            Parenthesized(Minus(D(1), Pow(Q(), Seq(D(2), i)))));
        return Disp(All(j, Nat(), Equal(Call(F.Id("qPoch"), j), product)));
    }

    private static Formula BinomFormula()
    {
        Formula n = F.Id("N"), k = F.Id("k");
        Formula value = new Formula.Fraction(Call(F.Id("qPoch"), n),
            Times(Call(F.Id("qPoch"), k), Call(F.Id("qPoch"), Seq(n, F.Minus, k))));
        return Disp(All(n, Nat(), All(k, Nat(), Equal(Call(F.Id("qBinom"), n, k), value))));
    }

    private static Formula CoeffFormula()
    {
        Formula n = F.Id("N"), k = F.Id("k");
        Formula factor = new Formula.Fraction(Plus(Pow(Q(), Seq(n, F.Minus, k)), Pow(Q(), k)),
            Plus(D(1), Pow(Q(), n)));
        return Disp(All(n, Nat(), All(k, Nat(),
            Equal(Call(F.Id("coeffF"), n, k), Times(factor, Call(F.Id("qBinom"), n, k))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("N"), k = F.Id("k"), p = F.Id("p");
        Formula polys = Seq(Mathbb, Grp(F.Id("Q")), OpenBracket, Q(), CloseBracket);
        Formula exists = Seq(Exists, Sp, p, Sp, Colon, Sp, polys, Comma, Sp,
            Equal(Call(F.Id("coeffF"), n, k), p));
        return Disp(Iff(F.Id("claim"), All(n, Nat(), All(k, Nat(), Implies(Le(k, n), exists)))));
    }
}
