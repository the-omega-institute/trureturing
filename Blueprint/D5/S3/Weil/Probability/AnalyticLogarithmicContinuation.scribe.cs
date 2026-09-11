using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Zeros.ActualZeroGeometryDocument;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class AnalyticLogarithmicContinuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/AnalyticLogarithmicContinuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classical analytic continuation preserves the actual scalar series and excludes zeros through analytic orders.",
        H("AnalyticLogarithmicContinuation"), Blocks(
            Describe.Lean(DescribeId.Create("quadratic-coefficients-summable"),
                DeclarationHandle.Create(Prefix + "quadratic_coefficients_summable"), H("All smaller radii have absolute convergence"),
                StatementSource.FromAuthor(All("a", Function(Natural, Complex), All("C", Real,
                    Imp(All("n", Natural, Le(Norm(Call("a", Id("n"))),
                        Multiply(Id("C"), Pow(Add(Id("n"), Num(1)), Num(2))))),
                        All("r", NNReal, Imp(Lt(Id("r"), Num(1)), ScalarSummable)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A bound on every coefficient is compared with polynomial-weighted geometric series, including radius zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("scalar-series-analytic-unit-disk"),
                DeclarationHandle.Create(Prefix + "scalar_series_analytic_unit_disk"), H("Analyticity of the original scalar sum"),
                StatementSource.FromAuthor(All("a", Function(Natural, Complex),
                    Imp(All("r", NNReal, Imp(Lt(Id("r"), Num(1)), ScalarSummable)),
                        AnalyticFormula(ScalarSum, UnitDisk)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing formal scalar-series radius and analyticity theorems apply to the actual coefficient sum throughout the unit disk."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("analytic-linear-ode-zero-free"),
                DeclarationHandle.Create(Prefix + "analytic_linear_ode_zero_free"), H("A nonzero analytic solution stays nonzero"),
                StatementSource.FromAuthor(OdeStatement(Imp(Everywhere(Equation), Everywhere(Nonzero)))) , AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a putative zero, differentiation lowers finite analytic order while multiplication by an analytic coefficient cannot. Connectedness and the nonzero initial value exclude infinite order."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-logarithmic-equation-zero-free"),
                DeclarationHandle.Create(Prefix + "local_logarithmic_equation_zero_free"), H("A local identity gives a global nonvanishing result"),
                StatementSource.FromAuthor(OdeStatement(Imp(LocalEquation(Id("p"), Equation),
                    And(Everywhere(Equation), Everywhere(Nonzero))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The analytic identity theorem extends the original derivative equation from a germ. Neither a global logarithm nor an already zero-free domain is supplied."))), DescribeRole.Theorem))));
    internal static Formula UnitDisk => Call("ball", Num(0), Num(1));
    internal static Formula AnalyticFormula(Formula f, Formula domain) => Call("AnalyticOnNhd", Complex, f, domain);
    internal static Formula Sum(Formula term) => F.Seq(F.Sum, F.Underscore,
        F.Grp(F.Id("n"), F.Eq, F.D(0)), F.Caret, F.Grp(F.Infty), term);
    internal static Formula ScalarSum => Lambda("z", Complex, Sum(Multiply(Call("a", Id("n")), Pow(Id("z"), Id("n")))));
    internal static Formula ScalarSummable => Call("Summable", Lambda("n", Natural,
        Multiply(Norm(Call("a", Id("n"))), Pow(Id("r"), Id("n")))));
    internal static Formula LocalEquation(Formula p, Formula equation) => F.Seq(
        F.Open, F.Forall, F.Caret, F.Grp(F.Id("f")), F.Sp, F.Id("z"), F.Sp, F.InMacro, F.Sp,
        F.Seq(F.Mathcal, F.Grp(F.Id("N")), F.Open, p, F.Close), F.Comma, F.Sp, equation, F.Close);
    private static Formula Equation => Equal(Call("deriv", Id("f"), Id("z")),
        Multiply(Call("g", Id("z")), Call("f", Id("z"))));
    private static Formula Nonzero => NotEqual(Call("f", Id("z")), Num(0));
    private static Formula Everywhere(Formula body) => All("z", Id("U"), body);
    private static Formula OdeStatement(Formula body) => All("U", Call("Set", Complex),
        All("f", Function(Complex, Complex), All("g", Function(Complex, Complex), All("p", Complex,
            Imp(Call("IsOpen", Id("U")), Imp(Call("IsPreconnected", Id("U")),
            Imp(AnalyticFormula(Id("f"), Id("U")), Imp(AnalyticFormula(Id("g"), Id("U")),
            Imp(new Formula.Relation(Id("p"), FormulaRelationOperator.MemberOf, Id("U")),
            Imp(NotEqual(Call("f", Id("p")), Num(0)), body))))))))));
}
