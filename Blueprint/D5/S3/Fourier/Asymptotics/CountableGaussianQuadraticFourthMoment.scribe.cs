using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CountableGaussianQuadraticFourthMomentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Square-summable centered Gaussian quadratic series converge in L4 with exact second and fourth moments.",
        H("Countable Gaussian Quadratic Fourth Moment"),
        Blocks(Describe.Lean(
            DescribeId.Create("countable-gaussian-quadratic-fourth-moment"),
            DeclarationHandle.Create(Module + "result"),
            H("Actual infinite sums and their moments"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple")),
            Blocks(
                Paragraph(Text("Let (Omega, Sigma, P) be any probability space. The countable family G(j) consists of independent real random variables with standard Gaussian law. Let a(j) be real coefficients whose squares are summable. Coefficients may be zero or negative, and their support may be infinite.")),
                Paragraph(Text("Write F(j)(omega)=a(j)(G(j)(omega)^2-1), T(s)(omega)=sum over j in the finite set s of F(j)(omega), and S=sum over j of a(j)^2. The theorem supplies proofs hm(j) that each actual term belongs to L4(P), and an element X of L4(P) to which their finite-subset sums converge in norm. The notation toLp(hm(j),F(j)) denotes the equivalence class of the actual function, modulo almost-everywhere equality. All integrals below use the measurable representative of X.")),
                Paragraph(Text("The representative X also belongs to L2(P), and eLpNorm(T(s)-X,2,P) tends to zero as s increases through all finite subsets. Its mean is zero, its second moment is 2S, and its fourth moment is 12S^2+48 sum over j of a(j)^4. In particular its fourth moment is at most fifteen times the square of its second moment. No higher integrability or series convergence is assumed.")),
                Paragraph(Text("For each finite subset, independence and the standard Gaussian even moments give the two exact moment identities. The fourth-power coefficient sum is at most the square of the square-sum, so every finite tail has fourth moment at most sixty times its coefficient square-sum squared. Completeness of L4 constructs the sum. Norm continuity passes the fourth moment to the limit, and exponent comparison gives the L2 and mean conclusions.")),
                Paragraph(Text("This is a coefficient-series moment calculation using classical Gaussian facts. The cited fixed-chaos literature provides related fourth-moment context; no claim of mathematical novelty is made. Identifying a prescribed spectral series with X requires equality of its L2 limit. This result alone asserts neither process tightness nor a stable limit."))),
            DescribeRole.Theorem))));

    private static Formula R => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula N => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Arrow(Formula x, Formula y) => F.Grp(F.Seq(x, F.To, F.Sp, y));
    private static Formula And(params Formula[] xs) => xs.Aggregate((x, y) => new Formula.Logic(x, FormulaLogicOperator.And, y));
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(x), domain)], body);
    private static Formula Lambda(string x, Formula domain, Formula body) =>
        F.Seq(F.Open, F.Id(x), F.Colon, domain, F.Mapsto, F.Sp, body, F.Close);
    private static Formula At(Formula f, params Formula[] args) =>
        F.Seq(f, F.Open, F.Seq(args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { F.Comma, x }).ToArray()), F.Close);
    private static Formula Pow(Formula x, byte n) => new Formula.Power(x, F.D(n));
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);

    private static Formula TheoremFormula()
    {
        Formula space = F.Id("Omega"), sigma = F.Id("Sigma"), p = F.Id("P"),
            g = F.Id("G"), a = F.Id("a"), x = F.Id("X"), hm = F.Id("hm"),
            j = F.Id("j"), omega = F.Id("omega"), s = F.Id("s");
        Formula term = Lambda("omega", space, Multiply(At(a, j),
            F.Seq(F.Open, Pow(At(At(g, j), omega), 2), F.Minus, F.D(1), F.Close)));
        Formula squareSum = Call("tsum", Lambda("j", N, Pow(At(a, j), 2)));
        Formula fourthSum = Call("tsum", Lambda("j", N, Pow(At(a, j), 4)));
        Formula integral(byte n) => Call("Integral", p, Lambda("omega", space, Pow(At(x, omega), n)));
        Formula partial = Lambda("omega", space, Call("finsetSum", s,
            Lambda("j", N, At(term, omega))));
        Formula hypotheses = And(Call("IsProbabilityMeasure", p),
            All("j", N, Call("HasLaw", At(g, j), Call("gaussianReal", F.D(0), F.D(1)), p)),
            Call("iIndepFun", g, p), Call("Summable", Lambda("j", N, Pow(At(a, j), 2))));
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("hm"),
                All("j", N, Call("MemLp", term, F.D(4), p))),
             new Formula.BoundVariable(FormulaIdentifier.Create("X"), Call("Lp", R, F.D(4), p))],
            And(Call("HasSum", Lambda("j", N, Call("toLp", At(hm, j), term)), x),
                Call("MemLp", x, F.D(2), p),
                Call("Tendsto", Lambda("s", Call("Finset", N),
                    Call("eLpNorm", F.Grp(F.Seq(partial, F.Minus, x)), F.D(2), p)),
                    F.Id("atTop"), Call("nhds", F.D(0))),
                Eq(integral(1), F.D(0)),
                Eq(integral(2), Multiply(F.D(2), squareSum)),
                Eq(integral(4), F.Seq(Multiply(F.D(1, 2), Pow(squareSum, 2)), F.Plus,
                    Multiply(F.D(4, 8), fourthSum))),
                new Formula.Relation(integral(4), FormulaRelationOperator.LessThanOrEqual,
                    Multiply(F.D(1, 5), Pow(integral(2), 2)))));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("Omega"), F.Id("Type")),
             new Formula.BoundVariable(FormulaIdentifier.Create("Sigma"), Call("MeasurableSpace", space)),
             new Formula.BoundVariable(FormulaIdentifier.Create("P"), Call("Measure", space, sigma)),
             new Formula.BoundVariable(FormulaIdentifier.Create("G"), Arrow(N, Arrow(space, R))),
             new Formula.BoundVariable(FormulaIdentifier.Create("a"), Arrow(N, R))],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }
}
