using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualLinearPeakDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An affine upper bound on any positive tail of the complete actual arithmetic kernel forces RH.",
        H("Affine Tails of the Actual Arithmetic Kernel"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-kernel-affine-tail-implies-rh"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_kernel_affine_tail_implies_rh"),
            H("An affine upper bound on an arbitrary positive tail forces RH"),
            StatementSource.FromAuthor(AffineTailClaim()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let tau>0 and let a,b be arbitrary real numbers. Suppose K(t)<=a*t+b "
                    + "for every real t>=tau, where K is the full literal "
                    + "ActualKernelLocalPositivity.K, with every Mangoldt ramp and "
                    + "trivial-zero correction retained. Then Mathlib RiemannHypothesis "
                    + "holds. This conditional criterion does not establish its arithmetic "
                    + "hypothesis or the original Robin converse.")),
                Paragraph(Text(
                    "The existing private engine is parameterized in place. For t>0 the "
                    + "actual integrated explicit formula identifies K(t) with "
                    + "k(t)=exp(-t/2)*Re(actualH(t)). On [tau,infinity), the denial "
                    + "makes a*t+b-k(t) nonnegative. Its ENNReal density against restricted "
                    + "volume defines mu; the closed and open cutoff restrictions agree "
                    + "because a singleton is Lebesgue-null. For r<0, "
                    + "|(a*t+b)*exp(r*t)| is bounded by "
                    + "(|a|*|t|+|b|)*exp(r*t). The zeroth and first exponential moments "
                    + "pay this bound for signed a,b. The actual exponential bound for k "
                    + "then proves mu's moments for r<-1/2, without finite total mass.")),
                Paragraph(Text(
                    "For P(z)=complexMGF(id,mu)(-z), the actual Laplace identity gives "
                    + "P=A-N/(z^2-1/4) initially in Re(z)>1/2. Keep the original "
                    + "normalization N=M*z-X'/X, X(z)=xiReading(z+1/2), M=firstLiMass. "
                    + "Here A=B+C, B=exp(-z*tau)*((a*tau+b)/z+a/z^2), and "
                    + "C=integral_(0,tau] exp(-z*t)*k(t) dt. Differentiating the "
                    + "restricted-volume transform pays B. Dominated parameter "
                    + "differentiation proves C entire, retaining the full finite prefix "
                    + "at the new cutoff without differentiating k.")),
                Paragraph(Text(
                    "First continue (z^2-1/4)*X*P=((z^2-1/4)*A-M*z)*X+X' "
                    + "on the actual open convex convergence domain of P inside Re(z)>0. "
                    + "Only local nonvanishing near positive real points is needed: "
                    + "the actual height theorem excludes real zeros of X. Endpoint "
                    + "normalization gives N(1/2)=0. The extension "
                    + "Q(z)=dslope(N,1/2,z)/(z+1/2) is holomorphic on this local "
                    + "nonzero domain. Analytic punctured uniqueness yields P=A-Q "
                    + "as a neighborhood germ at every interior convergence point there, "
                    + "including z=1/2; totalized division is not used as an extension.")),
                Paragraph(Text(
                    "Reflect z to -z and apply "
                    + "NonnegativeBoundary.integrable_exp_on_real_ray at target 0. "
                    + "The paid germs supply every real interior convergence point, "
                    + "so all negative exponential moments converge. The crossed identity "
                    + "now yields X'=G*X on the whole half-plane Re(z)>0, with "
                    + "G=(z^2-1/4)*(P-A)+M*z analytic even at the half-point and "
                    + "putative zeros of X. Using X(1/2)=1/2, the existing analytic "
                    + "linear ODE theorem excludes all such zeros; the existing "
                    + "right-half-strip reduction proves RH."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("actual-linear-peak-of-not-rh"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_linear_peak_of_not_rh"),
            H("The literal arithmetic kernel exceeds its linear envelope"),
            StatementSource.FromAuthor(Claim()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Here U is CompleteMertensPeak.U, containing all prime-power endpoints, "
                    + "and trivialT is the complete trivial-zero correction. The conclusion "
                    + "has no zero-simplicity, prime-number-theorem or additional transform "
                    + "hypothesis. It provides no quantitative upper bound for the first excursion.")),
                Paragraph(Text(
                    "Deny the excursion and apply actual_kernel_affine_tail_implies_rh "
                    + "with tau=log(10000), a=4, b=9. This positive cutoff permits the "
                    + "exact arithmetic identity for K at every point of that closed "
                    + "tail. The parameterized engine above includes the entire finite "
                    + "prefix at tau; no upper bound is extended to an earlier tail."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("actual-kernel-subexponential-implies-rh"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_kernel_subexponential_implies_rh"),
            H("The signed-kernel Laplace transform gives an analytic linear ODE"),
            StatementSource.FromAuthor(SubexponentialClaim()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let K be precisely ActualKernelLocalPositivity.K: "
                    + "K(t)=exp(-|t|/2)*(CompleteMertensPeak.U(exp(|t|)) "
                    + "- log(2*pi) + trivialT(|t|)). Every Mangoldt ramp and every "
                    + "trivial-zero correction is retained. Suppose that for every real "
                    + "beta>0 there exists a real C>0 such that for every real t, "
                    + "|K(t)|<=C*exp(beta*|t|). Then Mathlib RiemannHypothesis holds. "
                    + "C may depend on beta. The statement adds no positivity, RH, "
                    + "zero-free or logarithmic-derivative hypothesis.")),
                Paragraph(Text(
                    "For Re(z)>0 set L(z)=integral_(t>0) exp(-z*t)*K(t) dt, using "
                    + "the signed K itself. Continuity is reused from K_continuous. "
                    + "At a point z0 with a=Re(z0)>0, choose beta=a/4. Throughout "
                    + "the open neighborhood Re(z)>a/2, the derivative integrand is "
                    + "bounded in norm by C*t*exp(-a*t/4). The pinned Mathlib "
                    + "exponential-moment owner proves this majorant integrable; "
                    + "hasDerivAt_integral_of_dominated_loc_of_deriv_le then proves "
                    + "complex differentiability and hence analyticity on Re(z)>0. "
                    + "No derivative of K is taken.")),
                Paragraph(Text(
                    "On t>0 the actual integrated explicit formula identifies K(t) "
                    + "with linearKernel(t), whose complex form and Laplace formula "
                    + "follow from the complete integrated explicit formula. "
                    + "With X(z)=xiReading(z+1/2), M=firstLiMass and "
                    + "D(z)=z^2-1/4, the initial formula on Re(z)>1/2 is "
                    + "L=(M*z-X'/X)/D. Xi nonvanishing is used only on this initial "
                    + "half-plane, where the existing owner already supplies it.")),
                Paragraph(Text(
                    "Clear both denominators there to get D*X*L=M*z*X-X'. "
                    + "Both sides are analytic throughout the connected half-plane "
                    + "Re(z)>0, so analytic_continuation_unique extends this "
                    + "cross-multiplied identity. It yields X'=G*X with "
                    + "G=M*z-D*L analytic, including at z=1/2 and at any putative "
                    + "zero of X. There is no division by X in this continuation.")),
                Paragraph(Text(
                    "Use the existing shiftedXi_half fact X(1/2)=1/2 as the "
                    + "nonzero anchor. AnalyticLogarithmicContinuation's "
                    + "analytic_linear_ode_zero_free excludes every zero of X in "
                    + "Re(z)>0 without any simplicity premise. The existing "
                    + "RightHalfStripRiemannReduction converts this to Mathlib RH. "
                    + "This conditional criterion does not prove that the arithmetic "
                    + "K satisfies its subexponential hypothesis."))),
            DescribeRole.Theorem))));

    private static Formula AffineTailClaim()
    {
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var tau = F.Id("tau");
        var a = F.Id("a");
        var b = F.Id("b");
        var t = F.Id("t");
        var positiveTau = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, tau);
        var cutoff = new Formula.Relation(tau, FormulaRelationOperator.LessThanOrEqual, t);
        var bound = new Formula.Relation(Call("K", t), FormulaRelationOperator.LessThanOrEqual,
            Add(Multiply(a, t), b));
        var denial = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("t"), real,
            new Formula.Logic(cutoff, FormulaLogicOperator.Implies, bound));
        Formula claim = new Formula.Logic(positiveTau, FormulaLogicOperator.Implies,
            new Formula.Logic(denial, FormulaLogicOperator.Implies,
                Seq(Operatorname, Grp(F.Id("RiemannHypothesis")))));
        foreach (var name in new[] { "b", "a", "tau" })
            claim = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), real, claim);
        return Disp(claim);
    }

    private static Formula Claim()
    {
        var y = F.Id("y");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var rh = Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));
        var negativeHalf = new Formula.Fraction(new Formula.Negate(y), D(2));
        var arithmetic = Add(
            Subtract(Call("U", Call("exp", y)), Call("log", Multiply(D(2), F.Pi))),
            Call("trivialT", y));
        var excursion = new Formula.Relation(Add(Multiply(D(4), y), D(9)),
            FormulaRelationOperator.LessThan, Multiply(Call("exp", negativeHalf), arithmetic));
        var cutoff = new Formula.Relation(Call("log", D(1, 0, 0, 0, 0)),
            FormulaRelationOperator.LessThanOrEqual, y);
        return Disp(new Formula.Logic(Seq(Neg, Sp, rh), FormulaLogicOperator.Implies,
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("y"), real,
                new Formula.Logic(cutoff, FormulaLogicOperator.And, excursion))));
    }

    private static Formula SubexponentialClaim()
    {
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var beta = F.Id("beta");
        var c = F.Id("C");
        var t = F.Id("t");
        var zero = D(0);
        var positiveBeta = new Formula.Relation(zero, FormulaRelationOperator.LessThan, beta);
        var positiveC = new Formula.Relation(zero, FormulaRelationOperator.LessThan, c);
        var bound = new Formula.Relation(new Formula.Absolute(Call("K", t)),
            FormulaRelationOperator.LessThanOrEqual,
            Multiply(c, Call("exp", Multiply(beta, new Formula.Absolute(t)))));
        var growth = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("beta"), real,
            new Formula.Logic(positiveBeta, FormulaLogicOperator.Implies,
                new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("C"), real,
                    new Formula.Logic(positiveC, FormulaLogicOperator.And,
                        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("t"), real, bound)))));
        return Disp(new Formula.Logic(growth, FormulaLogicOperator.Implies,
            Seq(Operatorname, Grp(F.Id("RiemannHypothesis")))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
