using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CountableGaussianQuadraticJointLimitDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticJointLimit.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Dynamics/nualart2005multiple");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Countable Gaussian quadratic sums converge jointly with fixed old Gaussian coordinates to an independent Gaussian limit.",
        H("Joint Gaussian Quadratic Limit"),
        Blocks(Describe.Lean(
            DescribeId.Create("countable-gaussian-quadratic-joint-limit"),
            DeclarationHandle.Create(Module + "result"),
            H("Actual sums and the product limiting law"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("On any probability space, let X be a fixed almost-everywhere measurable vector in a finite-dimensional real Euclidean space. Its mean is arbitrary and its covariance may be singular. Each countable row G(n,j) consists of independent standard real Gaussian variables. Rows may be coupled arbitrarily. For every n and N, the actual joint law of X and the first N coordinates of row n is Gaussian. Independence between X and any row is not assumed.")),
                Paragraph(Text("The real coefficients a(n,j) are square summable in each row. Their supremum in absolute value tends to zero and their sum of squares tends to v/2 for a nonnegative variance v. Every centered weighted square belongs to L2. The series has an actual HasSum in L2, and the pair consisting of X and the representative of its sum Q(n) converges in distribution to the product of the law of X and the centered Gaussian law of variance v.")),
                Paragraph(Text("The result includes v=0, zero-dimensional X, infinite rows, negative coefficients, nonzero row/old correlations, and singular old covariance. The old vector is fixed as n varies. The rows do not need a common chosen noise basis.")),
                Paragraph(Text("For each real linear functional of X, finite Gaussian regression yields an independent residual and bounds the sum of squared regression coefficients by the fixed old variance. The mixed characteristic-function defect is controlled by the largest quadratic coefficient. L2 convergence passes this estimate to the countable sums. Combining the vanishing defect with the scalar Gaussian limit yields the product characteristic function, and the finite-dimensional Levy theorem gives weak convergence.")),
                Paragraph(Text("This is a joint finite-dimensional distribution theorem. A process mixing limit additionally requires the actual kernel representation, operator estimate, tightness, and measurable-cylinder approximation."))),
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
            n = F.Id("n"), j = F.Id("j"), q = F.Id("Q"), old = F.Id("X"), d = F.Id("d");
        Formula anj = At(a, n, j), gnj = At(g, n, j);
        Formula x = Lambda("omega", space, Multiply(anj,
            F.Seq(F.Open, new Formula.Power(At(gnj, omega), F.D(2)), F.Minus, F.D(1), F.Close)));
        Formula squares = Lambda("j", N, new Formula.Power(anj, F.D(2)));
        Formula l2 = Call("Lp", R, F.D(2), p);
        Formula oldSpace = Call("EuclideanSpace", R, Call("Fin", d));
        Formula joint = All("n", N, All("k", N, Call("HasGaussianLaw",
            Lambda("omega", space, Call("Pair", At(old, omega),
                Lambda("j", Call("Fin", F.Id("k")), At(At(g, n, j), omega)))), p)));
        Formula hypotheses = And(And(Call("IsProbabilityMeasure", p),
            And(Call("AEMeasurable", old, p), joint)),
            And(All("n", N, All("j", N, Call("HasLaw", gnj, Call("gaussianReal", F.D(0), F.D(1)), p))),
            And(All("n", N, Call("iIndepFun", At(g, n), p)),
            And(All("n", N, Call("Summable", squares)),
            And(Limit(Lambda("n", N, Call("sup", Lambda("j", N, new Formula.Absolute(anj)))), F.D(0)),
                Limit(Lambda("n", N, Call("tsum", squares)), new Formula.Fraction(v, F.D(2))))))));
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create("Q"), Arrow(N, l2))],
            And(All("n", N, All("j", N, Call("MemLp", x, F.D(2), p))),
            And(All("n", N, Call("HasSum", Lambda("j", N, Call("toLp", p, x)), At(q, n))),
                Call("TendstoInDistribution", Lambda("n", N,
                    Lambda("omega", space, Call("Pair", At(old, omega), At(Call("representative", At(q, n)), omega)))),
                    F.Id("atTop"), Call("id", Call("Product", oldSpace, R)), Lambda("n", N, p),
                    Call("ProductMeasure", Call("map", p, old), Call("gaussianReal", F.D(0), v))))));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("Omega"), F.Id("Type")),
             new Formula.BoundVariable(FormulaIdentifier.Create("Sigma"), Call("MeasurableSpace", space)),
             new Formula.BoundVariable(FormulaIdentifier.Create("P"), Call("Measure", space, sigma)),
             new Formula.BoundVariable(FormulaIdentifier.Create("d"), N),
             new Formula.BoundVariable(FormulaIdentifier.Create("X"), Arrow(space, oldSpace)),
             new Formula.BoundVariable(FormulaIdentifier.Create("G"), Arrow(N, Arrow(N, Arrow(space, R)))),
             new Formula.BoundVariable(FormulaIdentifier.Create("a"), Arrow(N, Arrow(N, R))),
             new Formula.BoundVariable(FormulaIdentifier.Create("v"), Nonnegative)],
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, conclusion)));
    }
}
