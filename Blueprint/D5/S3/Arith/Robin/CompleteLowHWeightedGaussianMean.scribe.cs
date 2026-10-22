using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class CompleteLowHWeightedGaussianMeanDocument : IScribeDocumentDefinition
{
    private static Formula Real => Seq(Mathbb, Grp(StrataLint.Scribe.FormulaDsl.Id("R")));

    private static Formula CallF(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula AddF(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Parameters(Formula conclusion)
    {
        var m = StrataLint.Scribe.DefinitionDsl.Id("m");
        return All("Z", CallF("CompleteZeroFamily"),
            All("m", Real, All("gamma", Real,
                Imp(new Formula.Relation(Num(0), FormulaRelationOperator.LessThan, m), conclusion))));
    }

    private static Formula FullLineStatement()
    {
        var z = StrataLint.Scribe.DefinitionDsl.Id("Z");
        var m = StrataLint.Scribe.DefinitionDsl.Id("m");
        var gamma = StrataLint.Scribe.DefinitionDsl.Id("gamma");
        var integrand = CallF("lowHIntegrand", z, m, gamma);
        var integral = CallF("integral", StrataLint.Scribe.DefinitionDsl.Id("y"), Real,
            CallF("lowHIntegrand", z, m, gamma, StrataLint.Scribe.DefinitionDsl.Id("y")));
        return Parameters(And(CallF("Integrable", integrand),
            Eq(integral, CallF("completeRealLineMean", z, m, gamma))));
    }

    private static Formula ExchangeStatement()
    {
        var z = StrataLint.Scribe.DefinitionDsl.Id("Z");
        var m = StrataLint.Scribe.DefinitionDsl.Id("m");
        var gamma = StrataLint.Scribe.DefinitionDsl.Id("gamma");
        var rhs = AddF(AddF(CallF("completeRealLineMean", z, m, gamma),
            CallF("positiveExtension", z, m, gamma)),
            CallF("negativeExtension", z, m, gamma));
        return Parameters(Eq(CallF("lowHMean", z, m, gamma), rhs));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute convergence makes the complete indexed Gaussian moment and extension identity valid.",
        H("Complete Low-Height Weighted Gaussian Mean"),
        Blocks(
            Paragraph(Text(
                "CompleteZeroFamily is indexed by all natural numbers; its zero map may repeat "
                + "a value. The open strip, absolute height above 10, summable reciprocal squares "
                + "with total below 2, finite inclusive shells and two-sided count floor(2*T^2) "
                + "retain every analytic multiplicity and both imaginary signs.")),
            Paragraph(Text(
                "The resolvent is bounded by the reciprocal square of the imaginary part. For "
                + "every real y and every h in [0,2], the exponential norm is at most exp(y)+exp(-2*y). "
                + "The two Gaussian endpoints give an integrable product majorant for the complete "
                + "norm series. Bochner integrability is proved before the sum and integral commute.")),
            Paragraph(Text(
                "For m >= 1, finite subsets of the natural index are partitioned by "
                + "floor(abs(Im(zero n))-10). The two-sided count and a geometric majorant yield "
                + "summability of shellWeight m (zero n) over all n and shellSum Z m <= "
                + "10000*exp(-100*m). The finite subsets are a proof device for the infinite sum.")),
            Paragraph(Text(
                "For every CompleteZeroFamily Z, every real m > 0 and every real gamma, "
                + "complete_zero_lowH_integrable proves IntegrableOn (lowHIntegrand Z m gamma) "
                + "on (1,infinity). Its source owner is CompleteLowHWeightedGaussianMean, with the "
                + "preserved CompleteLowHWeightedSpectralMean Lean namespace. The proof takes "
                + "complete_zero_lowH_product_integrable, applies integral_prod_left and moves the "
                + "fixed physical envelope outside the h integral. The product proof uses the full "
                + "reciprocal-square norm series and both Gaussian exponential endpoints. This exact "
                + "integrability fact supplies the first conjunct of the final weighted theorem.")),
            Describe.Lean(
                DescribeId.Create("complete-zero-full-line-moment"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/CompleteLowHWeightedGaussianMean.complete_zero_fullLine_integrable_and_moment"),
                H("Integrability and exact complete full-line mean"),
                StatementSource.FromAuthor(Disp(FullLineStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For m > 0 and arbitrary real gamma, the physical integrand is integrable on "
                    + "the whole real line and its integral equals the complete countable shell mean. "
                    + "The full complex cubic Gaussian identity retains center 16*m, the +2*z "
                    + "correction, the physical coefficient 3 and the actual weight 1+h.")))),
            Describe.Lean(
                DescribeId.Create("complete-zero-fubini-exchange"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/CompleteLowHWeightedGaussianMean.complete_zero_fubini_exchange"),
                H("The exact extension identity"),
                StatementSource.FromAuthor(Disp(ExchangeStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The positive extension is minus the integral over (0,1]; the negative "
                    + "extension is minus the integral over (-infinity,0). Whole-line integrability "
                    + "justifies the partition; the omitted singleton at zero is null. No finite "
                    + "truncation or additional analytic certificate is required."))))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Arith/Robin/CompleteLowHGaussianMoment")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticFourthMoment")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Arith/Robin/CompleteCoefficientLaplace"))]));
}
