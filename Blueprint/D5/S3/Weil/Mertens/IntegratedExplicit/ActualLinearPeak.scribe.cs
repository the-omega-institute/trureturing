using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class ActualLinearPeakDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Failure of RH forces a linear excursion of the complete actual arithmetic kernel.",
        H("A Linear Excursion of the Actual Arithmetic Kernel"),
        Blocks(Describe.Lean(
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
                    "Set T=log(10000) and k(t)=exp(-t/2)*Re(actualH(t)). The actual complete "
                    + "zero package supplies continuity and reality. Denying the excursion "
                    + "makes 4t+9-k(t) nonnegative on t>T. Use this as an ENNReal density "
                    + "against restricted volume; the resulting measure may have infinite "
                    + "total mass. The actual exponential bound proves its negative moments "
                    + "with parameter less than -1/2.")),
                Paragraph(Text(
                    "For P(z)=complexMGF(id,mu)(-z), the actual Laplace identity gives "
                    + "P=A-N/(z^2-1/4) initially in Re(z)>1/2. Here N=M*z-X'/X, "
                    + "X(z)=xiReading(z+1/2), M=firstLiMass and A=B+C. The polynomial tail "
                    + "B=exp(-z*T)*((4T+9)/z+4/z^2) is obtained by differentiating the "
                    + "restricted-volume transform. The compact correction C is entire by "
                    + "dominated parameter differentiation without differentiating k.")),
                Paragraph(Text(
                    "Continue the cross identity (z^2-1/4)*X*P=((z^2-1/4)*A-M*z)*X+X' "
                    + "on the actual open convex convergence domain. Every positive real "
                    + "belongs to the zero-free domain of X, by the original actual height "
                    + "theorem. Endpoint normalization gives N(1/2)=0, so the holomorphic "
                    + "quotient is dslope(N,1/2,z)/(z+1/2). Analytic punctured uniqueness "
                    + "supplies neighborhood equality also at 1/2.")),
                Paragraph(Text(
                    "NonnegativeBoundary.integrable_exp_on_real_ray applies at every real "
                    + "interior convergence point and forces all negative moments. The same "
                    + "cross identity now yields X'=G*X throughout Re(z)>0. The existing "
                    + "analytic_linear_ode_zero_free compares finite positive analytic "
                    + "orders at a hypothetical zero, handling all multiplicities. The "
                    + "right-half-strip reduction proves RH under denial. Finally the "
                    + "actual integrated explicit formula, used only at y>=T>0, restores "
                    + "the literal arithmetic conclusion."))),
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
