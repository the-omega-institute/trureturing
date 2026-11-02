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

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
