using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class GaussianQuadraticMixedDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform bound quantifies the dependence between Gaussian linear coordinates and diagonal quadratic sums.",
        H("Gaussian Quadratic Mixed Defect"),
        Blocks(Describe.Lean(
            DescribeId.Create("gaussian-quadratic-mixed-defect"),
            DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/GaussianQuadraticMixedDefect.result"),
            H("Correlated old coordinates and a finite Gaussian row"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let P be a probability measure on an arbitrary measurable space. Let G(j) be a finite independent family of standard real Gaussian variables. Let Y be any real random variable such that the actual pair of Y and the whole row G is jointly Gaussian. The mean of Y is unrestricted, and its variance may vanish. No independence of Y and G is assumed.")),
                Paragraph(Text("For arbitrary signed coefficients a(j) with absolute value at most a nonnegative M, set Q equal to the sum of a(j)(G(j)^2-1). The difference between the characteristic function of Y+Q at one and the product of the characteristic functions of Y and Q at one has norm at most M Var(Y) exp(M Var(Y)). The estimate is independent of the number of row coordinates and includes the empty row.")),
                Paragraph(Text("Regression uses b(j)=Cov(Y,G(j)). Its residual Y minus the sum of b(j)G(j) is jointly Gaussian and uncorrelated with the row, hence independent of it. Its nonnegative variance implies that the sum of b(j)^2 is at most Var(Y). The linear-plus-quadratic Gaussian integral and the exponential remainder bound then give the displayed estimate.")),
                Paragraph(Text("Scaling a by a test frequency gives the mixed characteristic-function estimate at that frequency. Passing the bound through L2 truncations allows countable quadratic sums; the finite estimate itself does not assert convergence in distribution."))),
            DescribeRole.Theorem))));

    private static Formula R => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Arrow(Formula x, Formula y) => F.Grp(F.Seq(x, F.To, F.Sp, y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Lambda(string name, Formula domain, Formula body) =>
        F.Seq(F.Open, F.Id(name), F.Colon, domain, F.Mapsto, F.Sp, body, F.Close);
    private static Formula At(Formula f, params Formula[] args) =>
        F.Seq(f, F.Open, F.Seq(args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { F.Comma, x }).ToArray()), F.Close);

    private static Formula TheoremFormula()
    {
        Formula space = F.Id("Omega"), sigma = F.Id("Sigma"), p = F.Id("P"), index = F.Id("J"),
            g = F.Id("G"), y = F.Id("Y"), a = F.Id("a"), m = F.Id("M"),
            j = F.Id("j"), w = F.Id("omega");
        Formula gj = At(g, j);
        Formula q = Call("sum", Lambda("j", index,
            Multiply(At(a, j), F.Grp(F.Seq(new Formula.Power(At(gj, w), F.D(2)), F.Minus, F.D(1))))));
        Formula qfun = Lambda("omega", space, q);
        Formula joint = Lambda("omega", space,
            Call("Pair", At(y, w), Lambda("j", index, At(gj, w))));
        Formula cf(Formula f) => Call("charFun", Call("map", p, f), F.D(1));
        Formula variance = Call("variance", y, p);
        Formula scale = Multiply(m, variance);
        Formula hyp = And(Call("IsProbabilityMeasure", p),
            And(All("j", index, Call("HasLaw", gj, Call("gaussianReal", F.D(0), F.D(1)), p)),
            And(Call("iIndepFun", g, p),
            And(Call("HasGaussianLaw", joint, p),
            And(F.Seq(F.D(0), F.Le, F.Sp, m),
                All("j", index, F.Seq(new Formula.Absolute(At(a, j)), F.Le, F.Sp, m)))))));
        Formula defect = Call("norm", F.Grp(F.Seq(
            cf(Lambda("omega", space, F.Seq(At(y, w), F.Plus, q))), F.Minus,
            Multiply(cf(y), cf(qfun)))));
        Formula bound = F.Seq(defect, F.Le, F.Sp, Multiply(scale, Call("exp", scale)));
        return F.Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("Omega"), F.Id("Type")),
             new Formula.BoundVariable(FormulaIdentifier.Create("Sigma"), Call("MeasurableSpace", space)),
             new Formula.BoundVariable(FormulaIdentifier.Create("J"), F.Id("FiniteType")),
             new Formula.BoundVariable(FormulaIdentifier.Create("P"), Call("Measure", space, sigma)),
             new Formula.BoundVariable(FormulaIdentifier.Create("G"), Arrow(index, Arrow(space, R))),
             new Formula.BoundVariable(FormulaIdentifier.Create("Y"), Arrow(space, R)),
             new Formula.BoundVariable(FormulaIdentifier.Create("a"), Arrow(index, R)),
             new Formula.BoundVariable(FormulaIdentifier.Create("M"), R)],
            new Formula.Logic(hyp, FormulaLogicOperator.Implies, bound)));
    }
}
