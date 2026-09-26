using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class TwoPhotonRabiConstraintPolynomialsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/reyesbustos2026twophotonrabi");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The constraint polynomials of the two-photon asymmetric quantum Rabi model factor into linear terms y + 2n(2n + 2rho - 1) at the critical coupling x = 1, and for x > 1 and nonnegative bias all their coefficients are positive, because the tridiagonal matrix behind them is positive definite.",
        H("The constraint polynomials of the two-photon Rabi model at and beyond the critical coupling"),
        Blocks(
            Node("constraint-poly", "The constraint polynomials", RecursionFormula(),
                "Definition 4.1 of the source, read as polynomials in y with real parameters x, bias eps and parity rho, and the index N of the constraint polynomial P_N.",
                "constraintPoly", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimDefinitionFormula(),
                "The first statement is taken for every real bias. The second statement is taken for bias eps >= 0, the sign the source uses when it derives the constraint condition; for eps = -2, N = 1 and rho = 0 one has P_1 = y - 2x + 4, which is negative at y = 0 once x > 2.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture for nonnegative bias", Disp(F.Id("claim")),
                "Part (a). At x = 1 the bias cancels from the recursion. In the basis of partial products Q_i = (y + lambda_1)...(y + lambda_i), with lambda_n = 2n(2n + 2rho - 1), the polynomial P_k(1, y) has coefficient C(k, i) 4^(k-i) (N-i-1)(N-i-2)...(N-k) (k+1)k...(i+2) at Q_i. Since y Q_i = Q_(i+1) - lambda_(i+1) Q_i, the recursion for these coefficients reduces to a polynomial identity that holds exactly when rho^2 = rho. At k = N every coefficient with i < N contains the factor N - N = 0, so P_N(1, y) = Q_N. Part (b). P_k(x, y) is det(y + J) for the symmetric tridiagonal matrix J(x) with diagonal entries d_k(x) = 2xk(4N + 2rho - 2k + 2eps + 1) - 4k(k + eps) and off-diagonal entries the square roots of the nonnegative couplings b_k x; expanding the determinant along the first row gives the recursion. By part (a) the eigenvalues of J(1) are the numbers lambda_n > 0, so J(1) is positive definite. For x >= 1 and eps >= 0, J(x) = sqrt(x) J(1) + D with D diagonal and D_k = 2k(sqrt(x) - 1)(sqrt(x)(4N + 2rho - 2k + 2eps + 1) + 2(k + eps)) >= 0, so J(x) is positive definite. Its eigenvalues mu_i are positive, P_N(x, y) is the product of the factors y + mu_i, and every coefficient is a sum of products of the mu_i, hence positive.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("reyes-bustos-wakayama-2026-two-photon-rabi-constraint-polynomials"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("rabi-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
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
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Product(params Formula[] factors)
    {
        var result = factors[0];
        for (var i = 1; i < factors.Length; i++) result = Times(result, factors[i]);
        return result;
    }
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula ProdOver(string variable, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(F.Id(variable), Sp, InMacro, Sp, domain)), Sp, body);
    private static Formula P(Formula x, Formula k) =>
        Call("constraintPoly", F.Id("N"), F.Id("rho"), F.Id("eps"), x, k);

    private static Formula RecursionFormula()
    {
        Formula n = F.Id("N"), rho = F.Id("rho"), eps = F.Id("eps"), x = F.Id("x"), y = F.Id("X");
        Formula k = F.Id("k");
        Formula kk = Add(k, D(2));
        Formula zero = Equal(P(x, D(0)), D(1));
        Formula one = Equal(P(x, D(1)), Add(y, Subtract(
            Product(D(2), x, Parenthesized(Subtract(Add(Add(Times(D(4), n), Times(D(2), rho)), Times(D(2), eps)), D(1)))),
            Times(D(4), Parenthesized(Add(D(1), eps))))));
        Formula diagonal = Subtract(
            Product(D(2), x, Parenthesized(kk),
                Parenthesized(Add(Add(Subtract(Add(Times(D(4), n), Times(D(2), rho)), Times(D(2), Parenthesized(kk))), Times(D(2), eps)), D(1)))),
            Product(D(4), Parenthesized(kk), Parenthesized(Add(kk, eps))));
        Formula m = Add(Subtract(n, Parenthesized(kk)), D(1));
        Formula coupling = Product(D(4), Parenthesized(kk), Parenthesized(Add(k, D(1))),
            Parenthesized(Add(Times(D(2), Parenthesized(m)), rho)),
            Parenthesized(Subtract(Add(Times(D(2), Parenthesized(m)), rho), D(1))), x);
        Formula step = All("k", Naturals(), Equal(P(x, kk),
            Subtract(Times(Parenthesized(Add(y, diagonal)), P(x, Add(k, D(1)))), Times(coupling, P(x, k)))));
        return Disp(And(And(zero, one), step));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("N"), rho = F.Id("rho"), eps = F.Id("eps"), x = F.Id("x"), i = F.Id("i"), j = F.Id("n");
        Formula factor = Add(F.Id("X"), Product(D(2), j, Parenthesized(Subtract(Add(Times(D(2), j), Times(D(2), rho)), D(1)))));
        Formula critical = All("eps", Reals(),
            Equal(P(D(1), n), ProdOver("n", Call("Finset.Icc", D(1), n), Parenthesized(factor))));
        Formula positive = All("eps", Reals(), Implies(AtMost(D(0), eps), All("x", Reals(),
            Implies(Less(D(1), x), All("i", Naturals(),
                Implies(AtMost(i, n), Less(D(0), Call("coeff", P(x, n), i))))))));
        Formula parity = Or(Equal(rho, D(0)), Equal(rho, D(1)));
        return All("N", Naturals(), All("rho", Reals(), Implies(parity, And(critical, positive))));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));
}
