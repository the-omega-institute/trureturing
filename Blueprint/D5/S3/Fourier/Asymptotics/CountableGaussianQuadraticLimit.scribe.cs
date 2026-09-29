using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CountableGaussianQuadraticLimitDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticLimit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Countable Gaussian quadratic rows have a Gaussian distributional limit when their maximal coefficient vanishes and their variance converges.",
        H("Countable Gaussian Quadratic Limit"),
        Blocks(Describe.Lean(
            DescribeId.Create("countable-gaussian-quadratic-limit"),
            DeclarationHandle.Create(Module + "result"),
            H("Actual square-integrable sums and their limiting law"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("Let (Omega, Sigma, P) be any probability space, and let G(n,j) be real random variables indexed by two natural numbers. Every G(n,j) has the standard Gaussian law. For each fixed n, the entire countable family G(n,j) is independent. No independence between different rows is required.")),
                Paragraph(Text("The real coefficients a(n,j) are square summable in j for every n. Their supremum in absolute value tends to zero, and the sum of their squares tends to v/2, where v is any nonnegative real number. Set X(n,j)(omega)=a(n,j)(G(n,j)(omega)^2-1). Every X(n,j) belongs to L2(P). The notation toLp below means its equivalence class modulo almost-everywhere equality.")),
                Paragraph(Text("There exist Q(n) in L2(P) such that the series of these equivalence classes has sum Q(n). HasSum is convergence of finite-subset sums in the L2 norm; the rows need not have finite support. The actual measurable representatives of Q(n) converge in distribution to the centered Gaussian measure of variance v. In particular v=0 gives the point mass at zero.")),
                Paragraph(Text("Centered standard Gaussian squares have second moment two and are orthogonal within each independent row. The Hilbert-space series theorem therefore constructs the actual sums. For real t, the characteristic function of Q(n) is the exponential of the absolutely convergent sum of -it a(n,j)-Log(1-2it a(n,j))/2. Linear terms cancel inside each summand, before summation.")),
                Paragraph(Text("Writing M(n)=sup_j |a(n,j)| and S(n)=sum_j a(n,j)^2, the absolute value of the summed exponent plus t^2 S(n) is at most (8/3)|t|^3 M(n)S(n) whenever 2|t|M(n)<=1/2. This error tends to zero, and Levy's characteristic-function theorem gives the stated limit. The classical fixed-chaos Gaussian criterion is described by Nualart and Peccati, Theorem 1; the argument here uses characteristic functions directly.")),
                Paragraph(Text("This statement concerns scalar coefficient arrays. Applying it to a specified kernel or Wiener integral requires its actual spectral identification. It does not assert a process limit, mixing with old noise, or tightness."))),
            DescribeRole.Theorem))));

    private static Formula R => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula N => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Nonnegative => F.Seq(R, F.Underscore, F.Grp(F.Seq(F.Ge, F.D(0))));
    private static Formula Arrow(Formula x, Formula y) => F.Grp(F.Seq(x, F.To, F.Sp, y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(x), domain)], body);
    private static Formula Lambda(string x, Formula domain, Formula body) =>
        F.Seq(F.Open, F.Id(x), F.Colon, domain, F.Mapsto, F.Sp, body, F.Close);
    private static Formula At(Formula f, params Formula[] args) =>
        F.Seq(f, F.Open, F.Seq(args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { F.Comma, x }).ToArray()), F.Close);
    private static Formula Limit(Formula f, Formula b) => Call("TendstoAtTop", f, b);

    private static Formula TheoremFormula()
    {
        Formula omega = F.Id("omega"), space = F.Id("Omega"), sigma = F.Id("Sigma"),
            p = F.Id("P"), g = F.Id("G"), a = F.Id("a"), v = F.Id("v"),
            n = F.Id("n"), j = F.Id("j"), q = F.Id("Q");
        Formula anj = At(a, n, j), gnj = At(g, n, j);
        Formula x = Lambda("omega", space, Multiply(anj,
            F.Seq(F.Open, new Formula.Power(At(gnj, omega), F.D(2)), F.Minus, F.D(1), F.Close)));
        Formula squares = Lambda("j", N, new Formula.Power(anj, F.D(2)));
        Formula l2 = Call("Lp", R, F.D(2), p);
        Formula hypotheses = And(Call("IsProbabilityMeasure", p),
            And(All("n", N, All("j", N, Call("HasLaw", gnj, Call("gaussianReal", F.D(0), F.D(1)), p))),
            And(All("n", N, Call("iIndepFun", At(g, n), p)),
            And(All("n", N, Call("Summable", squares)),
            And(Limit(Lambda("n", N, Call("sup", Lambda("j", N, new Formula.Absolute(anj)))), F.D(0)),
                Limit(Lambda("n", N, Call("tsum", squares)), new Formula.Fraction(v, F.D(2))))))));
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("Q"), Arrow(N, l2))],
            And(All("n", N, All("j", N, Call("MemLp", x, F.D(2), p))),
            And(All("n", N, Call("HasSum", Lambda("j", N, Call("toLp", p, x)), At(q, n))),
                Call("TendstoInDistribution", Lambda("n", N, Call("representative", At(q, n))),
                    F.Id("atTop"), Call("id", R), Lambda("n", N, p),
                    Call("gaussianReal", F.D(0), v)))));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("Omega"), F.Id("Type")),
             new Formula.BoundVariable(FormulaIdentifier.Create("Sigma"), Call("MeasurableSpace", space)),
             new Formula.BoundVariable(FormulaIdentifier.Create("P"), Call("Measure", space, sigma)),
             new Formula.BoundVariable(FormulaIdentifier.Create("G"), Arrow(N, Arrow(N, Arrow(space, R)))),
             new Formula.BoundVariable(FormulaIdentifier.Create("a"), Arrow(N, Arrow(N, R))),
             new Formula.BoundVariable(FormulaIdentifier.Create("v"), Nonnegative)],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }
}
