using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class UniformIntegralsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Subentropy/UniformIntegrals.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact scalar integrals for the maximally mixed two- and four-level subentropy kernels.",
        H("Uniform subentropy kernel integrals"), Blocks(
            Paragraph(Text("All integrals use real Lebesgue measure on the open half-line t>0. The reciprocal difference is integrated as a single function; its separate reciprocal terms are not integrable.")),
            GeneralNode("reciprocal-difference", "A convergent reciprocal difference", "reciprocal_difference",
                ReciprocalStatement(), "For positive a and b with a≤b, log(t+a)−log(t+b) has nonnegative derivative 1/(t+a)−1/(t+b), tends to zero at infinity, and has endpoint value log a−log b. The fundamental theorem of calculus gives both integrability and the stated integral."),
            GeneralNode("inverse-power", "Shifted inverse powers", "inverse_power",
                PowerStatement(), "For a>0 and a natural n, Mathlib integrableOn_add_rpow_Ioi_of_lt supplies integrability at exponent −n−2. Translation of Lebesgue measure and integral_Ioi_rpow_of_lt give the integral 1/((n+1)a^(n+1))."),
            Node("two", "The two-level integral", "integral_uniformTwo_kernel", TwoKernel(),
                Sub(Call("log", D(2)), Rat(D(1), D(2))),
                "The antiderivative is log(t+1/2)−log(t+1)+(1/4)/(t+1/2). Its limit at infinity is zero and its value at zero is −log 2+1/2."),
            Node("four", "The four-level integral", "integral_uniformFour_kernel", FourKernel(),
                Sub(Call("log", D(4)), Rat(D(1,3), D(1,2))),
                "The antiderivative is log(t+1/4)−log(t+1)+(3/8)/(t+1/4)−(1/32)/(t+1/4)^2+(1/768)/(t+1/4)^3. Its limit at infinity is zero and its value at zero is −log 4+13/12."))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula kernel,
        Formula value, string prose) => Describe.Lean(
            DescribeId.Create("subentropy-uniform-integrals-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Equal(Integral(kernel), value))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static DocumentBlock GeneralNode(string id, string title, string declaration,
        Formula statement, string prose) => Describe.Lean(
            DescribeId.Create("subentropy-uniform-integrals-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula And(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.And, q);
    private static Formula ImpliesFormula(Formula p, Formula q) => new Formula.Logic(p, FormulaLogicOperator.Implies, q);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Integrable(Formula body) => Call("IntegrableOn",
        Seq(LambdaLower, Sp, T, Colon, Real, Mapsto, body), Call("Ioi", D(0)));
    private static Formula ReciprocalStatement()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        Formula kernel = Sub(Rat(D(1), Add(T, a)), Rat(D(1), Add(T, b)));
        return All("a", Real, All("b", Real, ImpliesFormula(And(Less(D(0), a), Le(a, b)),
            And(Integrable(kernel), Equal(Integral(kernel), Sub(Call("log", b), Call("log", a)))))));
    }
    private static Formula PowerStatement()
    {
        Formula a = F.Id("a"), n = F.Id("n");
        Formula kernel = Rat(D(1), Pow(Add(T, a), Add(n, D(2))));
        Formula value = Rat(D(1), Mul(Add(n, D(1)), Pow(a, Add(n, D(1)))));
        return All("a", Real, ImpliesFormula(Less(D(0), a), All("n", Nat,
            And(Integrable(kernel), Equal(Integral(kernel), value)))));
    }
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Rat(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula T => F.Id("t");
    private static Formula Offset(int n) => Add(T, Rat(D(1), D((byte)n)));
    private static Formula Integral(Formula body) => Seq(Int, Underscore,
        Grp(new Formula.Relation(T, FormulaRelationOperator.GreaterThan, D(0))), Sp, body, Sp, Mathrm, Grp(F.Id("d")), Sp, T);
    private static Formula TwoKernel() => Sub(
        Sub(Rat(D(1), Offset(2)), Rat(D(1), Add(T, D(1)))),
        Rat(D(1), Mul(D(4), Pow(Offset(2), D(2)))));
    private static Formula FourKernel() => Sub(Add(Sub(
        Sub(Rat(D(1), Offset(4)), Rat(D(1), Add(T, D(1)))),
        Rat(D(3), Mul(D(8), Pow(Offset(4), D(2))))),
        Rat(D(1), Mul(D(1,6), Pow(Offset(4), D(3))))),
        Rat(D(1), Mul(D(2,5,6), Pow(Offset(4), D(4)))));
}
