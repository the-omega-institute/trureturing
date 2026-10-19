using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class TwoQubitBinegativityLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/TwoQubitBinegativityLowerBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/girard2017binegativity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every two-qubit density matrix, the binegativity is bounded below by the Girard–Gour curve at its negativity. The negative eigenvector of the partial transpose has a Schmidt product constrained from below by positivity of the density matrix.",
        H("The two-qubit binegativity lower bound at fixed negativity"),
        Blocks(
            Node("claim", "The lower bound of Girard and Gour", ClaimDefinitionFormula(),
                Blocks(
                    Paragraph(Text("Girard and Gour, Eq. (8), conjecture the displayed bound for every two-qubit density matrix sigma. A density matrix is positive semidefinite with trace one. Here nu is its negativity, c = sqrt(2 nu (nu + 1)) - nu, and N_2 is its binegativity. The symbol c denotes this function of nu, rather than the concurrence of an arbitrary state.")),
                    Paragraph(Text("For a self-adjoint matrix X, X_- is its positive semidefinite negative component, with X = X_+ - X_- and X_+ X_- = 0. All traces below are taken through their real parts, as in the negativity appearing in the statement. The binegativity is "),
                        Math(BinegativityFormula()), Text(".")),
                    Paragraph(Text("The partial transpose is on the second qubit: "),
                        Math(PartialTransposeFormula()), Text("."))),
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The lower bound holds for every two-qubit state", Disp(ClaimBody()),
                Blocks(Paragraph(Text("The partial transpose sigma^Gamma has at most one negative eigenvalue: every two-dimensional subspace of the two-qubit space contains a nonzero product vector, and the quadratic form of sigma^Gamma is nonnegative on product vectors. Thus a two-dimensional negative eigenspace is impossible. If there is a negative eigenvalue -lambda, local unitaries put its unit eigenvector in Schmidt form alpha |00> + beta |11>, with alpha and beta positive and alpha^2 + beta^2 = 1. These unitaries preserve both the negativity N and the binegativity N_2. In these coordinates write a = sigma_(00,00), d = sigma_(11,11), x = a + d, and u = -Re sigma_(01,10). The eigenvalue equations give u^2 = (a + lambda)(d + lambda), nu = 2 lambda, and (2 alpha beta)(x + nu) = 2u. Positivity on |01> + |10> gives 2u <= 1 - x; equivalently, one may use |01> - |10> after a local phase change. Consequently nu (2x + nu) <= (1 - x)^2, so x <= 1 - c. The same eigenvalue equations imply (2 alpha beta)^2 (x + nu)^2 >= nu (2x + nu), which forces 2 alpha beta >= c/sqrt((1 - c)^2 + c^2). Since (sigma^Gamma)_- = lambda |psi><psi|, its partial transpose has the single negative eigenvalue -lambda alpha beta. Therefore N_2(sigma) = (nu/2)(1 + 2 alpha beta), and the lower bound follows. When sigma^Gamma has no negative eigenvalue, its negative component is zero, so nu = c = N_2(sigma) = 0 and both sides vanish."))),
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("girard-2017-binegativity-lower-bound"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, BlockSequence commentary,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("tqbl-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            commentary, role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Let(Formula variable, Formula value, Formula body) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, variable, Sp, Colon, Sp, Reals(),
            Sp, Eq, Sp, value, Semi, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Square(Formula value) => new Formula.Power(Parenthesized(value), D(2));
    private static Formula Root(Formula value) => Seq(Sqrt, Grp(value));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Qubit() => Call("Fin", D(2));
    private static Formula Pairs() => Seq(Qubit(), Sp, F.Times, Sp, Qubit());
    private static Formula TwoQubit() =>
        Call("Matrix", Parenthesized(Pairs()), Parenthesized(Pairs()), Complexes());
    private static Formula Pt(Formula value) => new Formula.Power(Parenthesized(value), Gamma);
    private static Formula NegPart(Formula value) => new Formula.Subscript(Parenthesized(value), Minus);
    private static Formula ReTr(Formula value) => Seq(Re, Sp, Call("Tr", value));
    private static Formula Binegativity(Formula sigma) =>
        new Formula.Apply(new Formula.Subscript(F.Id("N"), D(2)), [sigma]);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Entry(Formula matrix, Formula i, Formula j, Formula k, Formula l) =>
        new Formula.Subscript(Parenthesized(matrix), Seq(Pair(i, j), Comma, Sp, Pair(k, l)));

    private static Formula BinegativityFormula()
    {
        Formula sigma = SigmaLower;
        Formula first = NegPart(Pt(sigma));
        Formula value = Add(ReTr(first), Mul(D(2), ReTr(NegPart(Pt(first)))));
        return All(sigma, TwoQubit(), Equal(Binegativity(sigma), value));
    }

    private static Formula PartialTransposeFormula()
    {
        Formula sigma = SigmaLower, i = F.Id("i"), j = F.Id("j"),
            k = F.Id("k"), l = F.Id("l");
        return All(sigma, TwoQubit(), All(i, Qubit(), All(j, Qubit(),
            All(k, Qubit(), All(l, Qubit(),
                Equal(Entry(Pt(sigma), i, j, k, l), Entry(sigma, i, l, k, j)))))));
    }

    private static Formula ClaimBody()
    {
        Formula sigma = SigmaLower, nu = Nu, c = F.Id("c");
        Formula negativity = Mul(D(2), ReTr(NegPart(Pt(sigma))));
        Formula curve = Subtract(Root(Mul(Mul(D(2), nu), Parenthesized(Add(nu, D(1))))), nu);
        Formula denominator = Root(Add(Square(Subtract(D(1), c)), Square(c)));
        Formula bound = Mul(new Formula.Fraction(nu, D(2)),
            Parenthesized(Add(D(1), new Formula.Fraction(c, denominator))));
        return All(sigma, TwoQubit(), Logic(Call("IsDensity", sigma), FormulaLogicOperator.Implies,
            Let(nu, negativity, Let(c, curve, AtMost(bound, Binegativity(sigma))))));
    }

    private static Formula ClaimDefinitionFormula() =>
        Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, ClaimBody()));
}
