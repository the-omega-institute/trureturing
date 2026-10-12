using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class UniformCDFConvergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise convergence to a continuous distribution function implies uniform convergence.",
        H("Uniform CDFConvergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monotone-cdf-pointwise-to-uniform"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.monotone_cdf_pointwise_to_uniform"),
                H("monotone_cdf_pointwise_to_uniform"),
                StatementSource.FromAuthor(Disp(All("F", new Formula.TypeArrow(Nat, new Formula.TypeArrow(Real, Real)), All("G", new Formula.TypeArrow(Real, Real), Imp(And(All("n", Nat, Call("Monotone", new Formula.Apply(V("F"), [V("n")]))), And(Call("Monotone", V("G")), And(Call("Continuous", V("G")), And(All("n", Nat, All("x", Real, Rel(new Formula.Number(0), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(V("F"), [V("n"), V("x")])))), And(All("n", Nat, All("x", Real, Rel(new Formula.Apply(V("F"), [V("n"), V("x")]), FormulaRelationOperator.LessThanOrEqual, new Formula.Number(1)))), And(All("x", Real, Rel(new Formula.Number(0), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(V("G"), [V("x")]))), And(All("x", Real, Rel(new Formula.Apply(V("G"), [V("x")]), FormulaRelationOperator.LessThanOrEqual, new Formula.Number(1))), And(Call("Tendsto", V("G"), V("atBot"), Call("nhds", new Formula.Number(0))), And(Call("Tendsto", V("G"), V("atTop"), Call("nhds", new Formula.Number(1))), All("x", Real, Call("Tendsto", LambdaFormula("n", Nat, new Formula.Apply(V("F"), [V("n"), V("x")])), V("atTop"), Call("nhds", new Formula.Apply(V("G"), [V("x")]))))))))))))), All("e", Real, Imp(Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, V("e")), new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, All("x", Real, Rel(new Formula.Absolute(Subtract(new Formula.Apply(V("F"), [V("n"), V("x")]), new Formula.Apply(V("G"), [V("x")]))), FormulaRelationOperator.LessThan, V("e")))), V("atTop")])))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(Paragraph(Text("Monotone distribution functions converging pointwise to a continuous distribution function converge uniformly on the whole real line. The proof uses a finite compact cover and the two limiting tails. See Durrett, Exercise 3.2.9."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charfun-limit-uniform-gaussian-cdf"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.charFun_limit_uniform_gaussian_cdf"),
                H("charFun_limit_uniform_gaussian_cdf"),
                StatementSource.FromAuthor(Disp(All("M", new Formula.TypeArrow(Nat, Call("ProbabilityMeasure", Real)), Imp(All("u", Real, Call("Tendsto", LambdaFormula("n", Nat, Call("charFun", Parenthesized(Seq(new Formula.Apply(V("M"), [V("n")]), Colon, Sp, Call("Measure", Real))), V("u"))), V("atTop"), Call("nhds", Parenthesized(Seq(new Formula.Apply(Qualified("Real", "exp"), [new Formula.Fraction(new Formula.Negate(Parenthesized(new Formula.Power(Parenthesized(V("u")), new Formula.Number(2)))), new Formula.Number(2))]), Colon, Sp, ComplexType))))), All("e", Real, Imp(Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, V("e")), new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, All("t", Real, Rel(new Formula.Absolute(Subtract(Call("cdf", Parenthesized(Seq(new Formula.Apply(V("M"), [V("n")]), Colon, Sp, Call("Measure", Real))), V("t")), new Formula.Apply(Call("cdf", Call("gaussianReal", new Formula.Number(0), new Formula.Number(1))), [V("t")]))), FormulaRelationOperator.LessThan, V("e")))), V("atTop")]))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(Paragraph(Text("Convergence of the characteristic functions to the standard Gaussian characteristic function gives uniform convergence of the cumulative distribution functions. The Gaussian CDF is Mathlib cdf (gaussianReal 0 1). Lévy continuity is combined with the uniform-CDF result of Durrett, Exercise 3.2.9."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula ComplexType => Seq(Mathbb, Grp(V("C")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula LambdaFormula(string name, Formula type, Formula body) =>
        Parenthesized(Seq(V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

}
