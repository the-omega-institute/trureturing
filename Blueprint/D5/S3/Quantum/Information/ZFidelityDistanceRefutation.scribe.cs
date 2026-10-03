using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ZFidelityDistanceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/ZFidelityDistanceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/nuradha2025multivariate");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nuradha, Mishra, Leditzky and Wilde (arXiv:2404.16101, J. Phys. A 58, 165304) ask in Open Question 3 whether sqrt(2(1 - F_z(rho, sigma))) is a distance measure for z in (1/2, 1) or z > 1, where F_z(rho, sigma) = Tr[(sigma^{1/(4z)} rho^{1/(2z)} sigma^{1/(4z)})^z]. At z = 2 it violates the triangle inequality for two rank-one qubit projections and a diagonal qubit state.",
        H("The z-fidelity distance violates the triangle inequality at z = 2"),
        Blocks(
            Node("fid", "The z-fidelity", FidelityFormula(),
                "Eq. (eq:z-fid-def): F_z(rho, sigma) is the trace of the z-th power of sigma^{1/(4z)} rho^{1/(2z)} sigma^{1/(4z)}, with real powers of positive semidefinite matrices taken in the continuous functional calculus; the real part of the trace is recorded.",
                "zFidelity", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("dist", "The distance of Open Question 3", DistanceFormula(),
                "The candidate distance is the square root of 2(1 - F_z(rho, sigma)).",
                "zDistance", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The asked distance property", ClaimFormula(),
                "Open Question 3 asks whether the distance is a distance measure for z in (1/2, 1) or z > 1. The statement is its triangle inequality, part of being a distance measure, for every such z, every dimension n and all n x n density matrices rho, sigma, tau.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("p", "The first projection", StateFormula("stateP", D(3)),
                "P is the projection onto (3, 1)/sqrt 10.",
                "stateP", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("q", "The diagonal state", QFormula(),
                "Q is the diagonal density matrix diag(16, 1)/17.",
                "stateQ", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("t", "The second projection", StateFormula("stateT", Seq(Minus, D(3))),
                "T is the projection onto (3, -1)/sqrt 10.",
                "stateT", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The triangle inequality fails at z = 2", Disp(new Formula.Not(F.Id("claim"))),
                "Every positive power of a positive idempotent is itself, so P and T are unchanged by the powers in F_2. The square roots of Q are diag(4, 1)/sqrt 17 and diag(2, 1)/17^{1/4}, by uniqueness of positive square roots. Hence F_2(P, T) = 256/625 and F_2(P, Q) = F_2(Q, T) = 361/(100 sqrt 17). The triangle inequality d(P, T) <= d(P, Q) + d(Q, T) would force 361/(100 sqrt 17) <= 2131/2500, but 9025^2 - 17 * 2131^2 = 4250888 > 0.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nuradha-2025-z-fidelity-distance"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("zfid-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula NumberSet(Formula name) => Seq(Mathbb, Grp(name));
    private static Formula Real() => NumberSet(F.Id("R"));
    private static Formula Complex() => NumberSet(F.Id("C"));
    private static Formula Fin(Formula n) => Call(F.Id("Fin"), n);
    private static Formula Mat(Formula n) => Call(F.Id("Matrix"), Fin(n), Fin(n), Complex());
    private static Formula Density(Formula rho) =>
        Logic(Call(F.Id("PosSemidef"), rho), FormulaLogicOperator.And, EqTo(Call(F.Id("tr"), rho), D(1)));
    private static Formula Fid(Formula z, Formula a, Formula b) => Call(F.Id("zFidelity"), z, a, b);
    private static Formula Dist(Formula z, Formula a, Formula b) => Call(F.Id("zDistance"), z, a, b);

    private static Formula FidelityFormula()
    {
        Formula z = F.Id("z"), rho = Rho, sigma = SigmaLower, n = F.Id("n");
        Formula outer = Pow(sigma, Frac(D(1), Mul(D(4), z)));
        Formula inner = Mul(Mul(outer, Pow(rho, Frac(D(1), Mul(D(2), z)))), outer);
        Formula value = Call(F.Id("re"), Call(F.Id("tr"), Pow(Parenthesized(inner), z)));
        return Disp(All(n, NumberSet(F.Id("N")), All(z, Real(), All(Seq(rho, Comma, Sp, sigma), Mat(n),
            EqTo(Fid(z, rho, sigma), value)))));
    }

    private static Formula DistanceFormula()
    {
        Formula z = F.Id("z"), rho = Rho, sigma = SigmaLower, n = F.Id("n");
        Formula value = Root(Mul(D(2), Parenthesized(Sub(D(1), Fid(z, rho, sigma)))));
        return Disp(All(n, NumberSet(F.Id("N")), All(z, Real(), All(Seq(rho, Comma, Sp, sigma), Mat(n),
            EqTo(Dist(z, rho, sigma), value)))));
    }

    private static Formula ClaimFormula()
    {
        Formula z = F.Id("z"), n = F.Id("n"), rho = Rho, sigma = SigmaLower, tau = Tau;
        Formula range = Logic(Logic(Rel(Frac(D(1), D(2)), FormulaRelationOperator.LessThan, z),
            FormulaLogicOperator.And, Rel(z, FormulaRelationOperator.LessThan, D(1))),
            FormulaLogicOperator.Or, Rel(D(1), FormulaRelationOperator.LessThan, z));
        Formula states = Logic(Logic(Density(rho), FormulaLogicOperator.And, Density(sigma)),
            FormulaLogicOperator.And, Density(tau));
        Formula triangle = LeTo(Dist(z, rho, tau), Add(Dist(z, rho, sigma), Dist(z, sigma, tau)));
        Formula body = All(z, Real(), Imp(range, All(n, NumberSet(F.Id("N")),
            All(Seq(rho, Comma, Sp, sigma, Comma, Sp, tau), Mat(n), Imp(states, triangle)))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, body));
    }

    private static Formula StateFormula(string name, Formula off)
    {
        Formula entries = Seq(OpenBracket, D(9), Comma, Sp, off, Semi, Sp, off, Comma, Sp, D(1), CloseBracket);
        return Disp(EqTo(F.Id(name), Mul(Frac(D(1), D(1, 0)), entries)));
    }

    private static Formula QFormula() =>
        Disp(EqTo(F.Id("stateQ"), Mul(Frac(D(1), D(1, 7)), Call(F.Id("diag"), D(1, 6), D(1)))));
}
