using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class BernoulliFourierControlDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Variance-weighted Fourier estimates control Bernoulli products.",
        H("Bernoulli Fourier Control"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bernoullivariance"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliVariance"),
                H("bernoulliVariance"),
                StatementSource.FromAuthor(Disp(All("p", Real, Equal(Call("bernoulliVariance", V("p")), Multiply(V("p"), Subtract(new Formula.Number(1), V("p"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The variance of a Bernoulli variable with success parameter p."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("centeredbernoulli"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliFourierControl.centeredBernoulli"),
                H("centeredBernoulli"),
                StatementSource.FromAuthor(Disp(All("p", Real, All("s", Real, Equal(Call("centeredBernoulli", V("p"), V("s")), Add(Multiply(Parenthesized(Seq(Subtract(new Formula.Number(1), V("p")), Colon, Sp, ComplexType)), new Formula.Apply(Qualified("Complex", "exp"), [Multiply(Parenthesized(Seq(Multiply(new Formula.Negate(Parenthesized(V("s"))), V("p")), Colon, Sp, ComplexType)), Qualified("Complex", "I"))])), Multiply(Parenthesized(Seq(V("p"), Colon, Sp, ComplexType)), new Formula.Apply(Qualified("Complex", "exp"), [Multiply(Parenthesized(Seq(Multiply(V("s"), Subtract(new Formula.Number(1), V("p"))), Colon, Sp, ComplexType)), Qualified("Complex", "I"))])))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The characteristic function of the centered Bernoulli variable. Real coefficients and phases are coerced into the complex numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("centered-bernoulli-product-gaussian-error"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliFourierControl.centered_bernoulli_product_gaussian_error"),
                H("centered_bernoulli_product_gaussian_error"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Real), All("u", Real, Imp(And(All("i", Call("Fin", V("m")), And(Rel(new Formula.Number(0), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(V("p"), [V("i")])), Rel(new Formula.Apply(V("p"), [V("i")]), FormulaRelationOperator.LessThanOrEqual, new Formula.Number(1)))), Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, Seq(new Formula.Subscript(Sum, Seq(V("j"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("bernoulliVariance", new Formula.Apply(V("p"), [V("j")])))))), Rel(new Formula.Norm(Subtract(Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("centeredBernoulli", new Formula.Apply(V("p"), [V("i")]), new Formula.Fraction(V("u"), new Formula.Apply(Qualified("Real", "sqrt"), [Seq(new Formula.Subscript(Sum, Seq(V("j"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("bernoulliVariance", new Formula.Apply(V("p"), [V("j")]))))]))))), Parenthesized(Seq(new Formula.Apply(Qualified("Real", "exp"), [new Formula.Fraction(new Formula.Negate(Parenthesized(new Formula.Power(Parenthesized(V("u")), new Formula.Number(2)))), new Formula.Number(2))]), Colon, Sp, ComplexType)))), FormulaRelationOperator.LessThanOrEqual, Add(new Formula.Fraction(new Formula.Power(Parenthesized(new Formula.Absolute(V("u"))), new Formula.Number(3)), Multiply(new Formula.Number(6), new Formula.Apply(Qualified("Real", "sqrt"), [Seq(new Formula.Subscript(Sum, Seq(V("j"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("bernoulliVariance", new Formula.Apply(V("p"), [V("j")]))))]))), new Formula.Fraction(new Formula.Power(Parenthesized(V("u")), new Formula.Number(4)), Multiply(new Formula.Number(32), Seq(new Formula.Subscript(Sum, Seq(V("j"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("bernoulliVariance", new Formula.Apply(V("p"), [V("j")])))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The summed third-moment remainder and the Gaussian factor remainder give a variance-weighted bound uniform in the Bernoulli parameters."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("centered-bernoulli-charfun-tendsto"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliFourierControl.centered_bernoulli_charFun_tendsto"),
                H("centered_bernoulli_charFun_tendsto"),
                StatementSource.FromAuthor(Disp(All("m", new Formula.TypeArrow(Nat, Nat), All("p", All("n", Nat, new Formula.TypeArrow(Call("Fin", new Formula.Apply(V("m"), [V("n")])), Real)), All("V", new Formula.TypeArrow(Nat, Real), All("u", Real, Imp(And(new Formula.Apply(Qualified("Filter", "Eventually"), [LambdaFormula("n", Nat, And(All("i", Call("Fin", new Formula.Apply(V("m"), [V("n")])), And(Rel(new Formula.Number(0), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(V("p"), [V("n"), V("i")])), Rel(new Formula.Apply(V("p"), [V("n"), V("i")]), FormulaRelationOperator.LessThanOrEqual, new Formula.Number(1)))), And(Equal(new Formula.Apply(V("V"), [V("n")]), Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, Call("Fin", new Formula.Apply(V("m"), [V("n")])))), Sp, Parenthesized(Call("bernoulliVariance", new Formula.Apply(V("p"), [V("n"), V("i")]))))), Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, new Formula.Apply(V("V"), [V("n")]))))), V("atTop")]), And(Call("Tendsto", V("V"), V("atTop"), V("atTop")), All("n", Nat, Equal(new Formula.Apply(V("V"), [V("n")]), Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, Call("Fin", new Formula.Apply(V("m"), [V("n")])))), Sp, Parenthesized(Call("bernoulliVariance", new Formula.Apply(V("p"), [V("n"), V("i")])))))))), Call("Tendsto", LambdaFormula("n", Nat, Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", new Formula.Apply(V("m"), [V("n")])))), Sp, Parenthesized(Call("centeredBernoulli", new Formula.Apply(V("p"), [V("n"), V("i")]), new Formula.Fraction(V("u"), new Formula.Apply(Qualified("Real", "sqrt"), [new Formula.Apply(V("V"), [V("n")])])))))), V("atTop"), Call("nhds", Parenthesized(Seq(new Formula.Apply(Qualified("Real", "exp"), [new Formula.Fraction(new Formula.Negate(Parenthesized(new Formula.Power(Parenthesized(V("u")), new Formula.Number(2)))), new Formula.Number(2))]), Colon, Sp, ComplexType))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Asymptotics/bender1973limits")),
                Blocks(Paragraph(Text("Divergence of row variances gives the standard Gaussian characteristic function at each fixed frequency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("centeredbernoulli-eq-phase"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliFourierControl.centeredBernoulli_eq_phase"),
                H("centeredBernoulli_eq_phase"),
                StatementSource.FromAuthor(Disp(All("p", Real, All("s", Real, Equal(Call("centeredBernoulli", V("p"), V("s")), Multiply(new Formula.Apply(Qualified("Complex", "exp"), [Multiply(Parenthesized(Seq(Multiply(new Formula.Negate(Parenthesized(V("s"))), V("p")), Colon, Sp, ComplexType)), Qualified("Complex", "I"))]), Add(Parenthesized(Seq(Subtract(new Formula.Number(1), V("p")), Colon, Sp, ComplexType)), Multiply(Parenthesized(Seq(V("p"), Colon, Sp, ComplexType)), new Formula.Apply(Qualified("Complex", "exp"), [Multiply(Parenthesized(Seq(V("s"), Colon, Sp, ComplexType)), Qualified("Complex", "I"))]))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Centering factors the characteristic function into a phase and the uncentered Bernoulli characteristic function."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("normalized-bernoulli-product-envelope"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliFourierControl.normalized_bernoulli_product_envelope"),
                H("normalized_bernoulli_product_envelope"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Real), All("V", Real, All("u", Real, Imp(And(Rel(new Formula.Number(0), FormulaRelationOperator.LessThan, V("V")), And(Equal(V("V"), Seq(new Formula.Subscript(Sum, Seq(V("j"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("bernoulliVariance", new Formula.Apply(V("p"), [V("j")]))))), Rel(new Formula.Absolute(V("u")), FormulaRelationOperator.LessThanOrEqual, Multiply(Qualified("Real", "pi"), new Formula.Apply(Qualified("Real", "sqrt"), [V("V")]))))), Rel(new Formula.Norm(Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("centeredBernoulli", new Formula.Apply(V("p"), [V("i")]), new Formula.Fraction(V("u"), new Formula.Apply(Qualified("Real", "sqrt"), [V("V")])))))), FormulaRelationOperator.LessThanOrEqual, new Formula.Apply(Qualified("Real", "exp"), [new Formula.Fraction(new Formula.Negate(Parenthesized(Multiply(new Formula.Number(2), new Formula.Power(Parenthesized(V("u")), new Formula.Number(2))))), new Formula.Power(Parenthesized(Qualified("Real", "pi")), new Formula.Number(2)))]))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the principal frequency interval, the normalized product is bounded by exp(-2u^2/pi^2), an integrable envelope independent of the row."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoulliweight"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliWeight"),
                H("bernoulliWeight"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), All("x", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("Bool")))), Equal(Call("bernoulliWeight", V("p"), V("x")), Seq(new Formula.Subscript(Prod, Seq(V("i"), Colon, Sp, Call("Fin", V("m")))), Sp, Parenthesized(Call("ite", Equal(new Formula.Apply(V("x"), [V("i")]), V("true")), Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real)), Subtract(new Formula.Number(1), Parenthesized(Seq(new Formula.Apply(V("p"), [V("i")]), Colon, Sp, Real)))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The atom weight is the product of p(i) for true coordinates and 1-p(i) for false coordinates. The conditional tests whether x(i) is true."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bernoullispace"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliSpace"),
                H("bernoulliSpace"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), Equal(Call("bernoulliSpace", V("p")), new Formula.Apply(Qualified("Measure", "pi"), [LambdaFormula("i", Call("Fin", V("m")), Call("bernoulliMeasure", V("true"), V("false"), new Formula.Apply(V("p"), [V("i")])))])))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The probability space is the product of the two-point measures bernoulliMeasure true false p(i)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bernoullispaceprobability"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulliSpaceProbability"),
                H("bernoulliSpaceProbability"),
                StatementSource.FromAuthor(Disp(All("m", Nat, All("p", new Formula.TypeArrow(Call("Fin", V("m")), Seq(Operatorname, Grp(V("unitInterval")))), Call("IsProbabilityMeasure", Call("bernoulliSpace", V("p"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product of the Bernoulli probability measures is a probability measure."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bernoulli-atom"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/BernoulliFourierControl.bernoulli_atom"),
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
