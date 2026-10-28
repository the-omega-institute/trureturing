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
                DescribeId.Create("gaussian-charfun-standard"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.gaussian_charFun_standard"),
                H("gaussian_charFun_standard"),
                StatementSource.FromAuthor(Disp(All("u", Real,
                    Equal(Call("charFun", Call("gaussianReal", new Formula.Number(0), new Formula.Number(1)), V("u")),
                        Parenthesized(Seq(new Formula.Apply(Qualified("Real", "exp"),
                            [new Formula.Fraction(new Formula.Negate(new Formula.Power(V("u"), new Formula.Number(2))), new Formula.Number(2))]),
                            Colon, Sp, ComplexType)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The characteristic function of the standard Gaussian at a real frequency u is exp(-u^2/2)."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("gaussian-factor-norm-le"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.gaussian_factor_norm_le"),
                H("gaussian_factor_norm_le"),
                StatementSource.FromAuthor(Disp(All("v", Real, All("s", Real,
                    Imp(Rel(new Formula.Number(0), FormulaRelationOperator.LessThanOrEqual, V("v")),
                        Rel(new Formula.Norm(Parenthesized(Seq(new Formula.Apply(Qualified("Real", "exp"),
                            [new Formula.Fraction(Multiply(new Formula.Negate(new Formula.Power(V("s"), new Formula.Number(2))), V("v")), new Formula.Number(2))]),
                            Colon, Sp, ComplexType))), FormulaRelationOperator.LessThanOrEqual, new Formula.Number(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Gaussian factor with nonnegative variance has complex norm at most one at every real frequency."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("charfun-limit-uniform-gaussian-cdf"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.charFun_limit_uniform_gaussian_cdf"),
                H("charFun_limit_uniform_gaussian_cdf"),
                StatementSource.FromAuthor(Disp(All("M", new Formula.TypeArrow(Nat, Call("ProbabilityMeasure", Real)), Imp(All("u", Real, Call("Tendsto", LambdaFormula("n", Nat, Call("charFun", Parenthesized(Seq(new Formula.Apply(V("M"), [V("n")]), Colon, Sp, Call("Measure", Real))), V("u"))), V("atTop"), Call("nhds", Parenthesized(Seq(new Formula.Apply(Qualified("Real", "exp"), [new Formula.Fraction(new Formula.Negate(Parenthesized(new Formula.Power(Parenthesized(V("u")), new Formula.Number(2)))), new Formula.Number(2))]), Colon, Sp, ComplexType))))), All("e", Real, Imp(Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, V("e")), new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, All("t", Real, Rel(new Formula.Absolute(Subtract(Call("cdf", Parenthesized(Seq(new Formula.Apply(V("M"), [V("n")]), Colon, Sp, Call("Measure", Real))), V("t")), new Formula.Apply(Call("cdf", Call("gaussianReal", new Formula.Number(0), new Formula.Number(1))), [V("t")]))), FormulaRelationOperator.LessThan, V("e")))), V("atTop")]))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/durrett2019probability")),
                Blocks(Paragraph(Text("Convergence of the characteristic functions to the standard Gaussian characteristic function gives uniform convergence of the cumulative distribution functions. The Gaussian CDF is Mathlib cdf (gaussianReal 0 1). Lévy continuity is combined with the uniform-CDF result of Durrett, Exercise 3.2.9."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("centeredbernoulli"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.centeredBernoulli"),
                H("centeredBernoulli"),
                StatementSource.FromAuthor(Disp(All("p", Real, All("s", Real, Equal(Call("centeredBernoulli", V("p"), V("s")), Add(Multiply(Parenthesized(Seq(Subtract(new Formula.Number(1), V("p")), Colon, Sp, ComplexType)), new Formula.Apply(Qualified("Complex", "exp"), [Multiply(Parenthesized(Seq(Multiply(new Formula.Negate(Parenthesized(V("s"))), V("p")), Colon, Sp, ComplexType)), Qualified("Complex", "I"))])), Multiply(Parenthesized(Seq(V("p"), Colon, Sp, ComplexType)), new Formula.Apply(Qualified("Complex", "exp"), [Multiply(Parenthesized(Seq(Multiply(V("s"), Subtract(new Formula.Number(1), V("p"))), Colon, Sp, ComplexType)), Qualified("Complex", "I"))])))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The characteristic function of the centered Bernoulli variable. Real coefficients and phases are coerced into the complex numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("centered-bernoulli-charfun-tendsto"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.centered_bernoulli_charFun_tendsto"),
                H("centered_bernoulli_charFun_tendsto"),
                StatementSource.FromAuthor(Disp(All("m", new Formula.TypeArrow(Nat, Nat), All("p", All("n", Nat, new Formula.TypeArrow(Call("Fin", new Formula.Apply(V("m"), [V("n")])), Real)), All("V", new Formula.TypeArrow(Nat, Real), All("u", Real, Imp(And(new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, And(All("i", Call("Fin", new Formula.Apply(V("m"), [V("n")])), And(Rel(new Formula.Number(0), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(V("p"), [V("n"), V("i")])), Rel(new Formula.Apply(V("p"), [V("n"), V("i")]), FormulaRelationOperator.LessThanOrEqual, new Formula.Number(1)))), And(Equal(new Formula.Apply(V("V"), [V("n")]), Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, Call("Fin", new Formula.Apply(V("m"), [V("n")])))), Sp, Parenthesized(Multiply(new Formula.Apply(V("p"), [V("n"), V("i")]), Parenthesized(Subtract(new Formula.Number(1), new Formula.Apply(V("p"), [V("n"), V("i")]))))))), Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, new Formula.Apply(V("V"), [V("n")]))))), V("atTop")]), And(Call("Tendsto", V("V"), V("atTop"), V("atTop")), All("n", Nat, Equal(new Formula.Apply(V("V"), [V("n")]), Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, Call("Fin", new Formula.Apply(V("m"), [V("n")])))), Sp, Parenthesized(Multiply(new Formula.Apply(V("p"), [V("n"), V("i")]), Parenthesized(Subtract(new Formula.Number(1), new Formula.Apply(V("p"), [V("n"), V("i")])))))))))), Call("Tendsto", LambdaFormula("n", Nat, Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", new Formula.Apply(V("m"), [V("n")])))), Sp, Parenthesized(Call("centeredBernoulli", new Formula.Apply(V("p"), [V("n"), V("i")]), new Formula.Fraction(V("u"), new Formula.Apply(Qualified("Real", "sqrt"), [new Formula.Apply(V("V"), [V("n")])])))))), V("atTop"), Call("nhds", Parenthesized(Seq(new Formula.Apply(Qualified("Real", "exp"), [new Formula.Fraction(new Formula.Negate(Parenthesized(new Formula.Power(Parenthesized(V("u")), new Formula.Number(2)))), new Formula.Number(2))]), Colon, Sp, ComplexType))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/bender1973limits")),
                Blocks(Paragraph(Text("Divergence of row variances gives the standard Gaussian characteristic function at each fixed frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("centeredbernoulli-eq-phase"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.centeredBernoulli_eq_phase"),
                H("centeredBernoulli_eq_phase"),
                StatementSource.FromAuthor(Disp(All("p", Real, All("s", Real, Equal(Call("centeredBernoulli", V("p"), V("s")), Multiply(new Formula.Apply(Qualified("Complex", "exp"), [Multiply(Parenthesized(Seq(Multiply(new Formula.Negate(Parenthesized(V("s"))), V("p")), Colon, Sp, ComplexType)), Qualified("Complex", "I"))]), Add(Parenthesized(Seq(Subtract(new Formula.Number(1), V("p")), Colon, Sp, ComplexType)), Multiply(Parenthesized(Seq(V("p"), Colon, Sp, ComplexType)), new Formula.Apply(Qualified("Complex", "exp"), [Multiply(Parenthesized(Seq(V("s"), Colon, Sp, ComplexType)), Qualified("Complex", "I"))]))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Centering factors the characteristic function into a phase and the uncentered Bernoulli characteristic function."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("normalized-bernoulli-product-envelope"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.normalized_bernoulli_product_envelope"),
                H("normalized_bernoulli_product_envelope"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Real), All("V", Real, All("u", Real, Imp(And(Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, V("V")), And(Equal(V("V"), Seq(new Formula.Subscript(Sum, Seq(V("j"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Multiply(new Formula.Apply(V("p"), [V("j")]), Parenthesized(Subtract(new Formula.Number(1), new Formula.Apply(V("p"), [V("j")]))))))), Rel(new Formula.Absolute(V("u")), FormulaRelationOperator.LessThanOrEqual, Multiply(Qualified("Real", "pi"), new Formula.Apply(Qualified("Real", "sqrt"), [V("V")]))))), Rel(new Formula.Norm(Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("centeredBernoulli", new Formula.Apply(V("p"), [V("i")]), new Formula.Fraction(V("u"), new Formula.Apply(Qualified("Real", "sqrt"), [V("V")])))))), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(Qualified("Real", "exp"), [new Formula.Fraction(new Formula.Negate(Parenthesized(Multiply(new Formula.Number(2), new Formula.Power(Parenthesized(V("u")), new Formula.Number(2))))), new Formula.Power(Parenthesized(Qualified("Real", "pi")), new Formula.Number(2)))]))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the principal frequency interval, the normalized product is bounded by exp(-2u^2/pi^2), an integrable envelope independent of the row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoulliweight"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulliWeight"),
                H("bernoulliWeight"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), All("x", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("Bool")))), Equal(Call("bernoulliWeight", V("p"), V("x")), Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("ite", Equal(new Formula.Apply(V("x"), [V("i")]), V("true")), Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real)), Subtract(new Formula.Number(1), Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real)))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The atom weight is the product of p(i) for true coordinates and 1-p(i) for false coordinates. The conditional tests whether x(i) is true."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bernoullispace"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulliSpace"),
                H("bernoulliSpace"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), Equal(Call("bernoulliSpace", V("p")), new Formula.Apply(Qualified("Measure", "pi"), [LambdaFormula("i", Call("Fin", V("m")), Call("bernoulliMeasure", V("true"), V("false"), new Formula.Apply(V("p"), [V("i")])))])))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The probability space is the product of the two-point measures bernoulliMeasure true false p(i)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bernoullispaceprobability"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulliSpaceProbability"),
                H("bernoulliSpaceProbability"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), Call("IsProbabilityMeasure", Call("bernoulliSpace", V("p"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product of the Bernoulli probability measures is a probability measure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bernoulli-atom"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/UniformCDFConvergence.bernoulli_atom"),
                H("bernoulli_atom"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), All("x", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("Bool")))), Equal(new Formula.Apply(Qualified("Measure", "real"), [Call("bernoulliSpace", V("p")), new Formula.SetLiteral([V("x")])]), Call("bernoulliWeight", V("p"), V("x")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real measure of a singleton is its product weight."))),
                DescribeRole.Lemma))));

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
