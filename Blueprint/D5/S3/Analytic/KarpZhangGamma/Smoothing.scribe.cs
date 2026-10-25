using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangGamma;

internal sealed class SmoothingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficientwise balancing of exponential derivatives.",
        H("Finite exponential smoothing"), Blocks(
            Entry("karp-zhang-gamma-binomial-product", "binomialProduct", "Factorial-scaled coefficient",
                "For real sequences f,g and natural N, binomialProduct(f,g,N) is the sum over r=0,...,N of Nat.choose(N,r) times f(r)g(N-r), with the binomial coefficient cast to the reals. It is N factorial times the ordinary coefficient of the product of the exponential generating series of f and g.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-product-coeff", "productCoeff", "Ordinary coefficient",
                "For real sequences f,g and natural N, productCoeff(f,g,N) is the sum over r=0,...,N of f(r)g(N-r) divided by r factorial times (N-r) factorial. This is an ordinary finite Cauchy coefficient, without convergence assumptions.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-balanced-product", "balanced_product", "General balancing inequality",
                "Let y satisfy D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave. For natural L,R,u,v satisfying L <= u, L <= v, u <= R, v <= R and u+v=L+R, y(L)y(R) <= y(u)y(v). The proof reuses the existing balanced_step theorem at fixed index sum, including sequences whose lower support boundary is positive.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-binomial-product-succ", "binomialProduct_succ", "Finite Leibniz recurrence",
                "For every pair of real sequences f,g and natural N, binomialProduct(f,g,N+1) equals binomialProduct(r maps to f(r+1),g,N) plus binomialProduct(f,r maps to g(r+1),N). Finset.sum_choose_succ_mul supplies the recurrence for the function (i,j) maps to f(i)g(j), retaining both endpoint terms exactly.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-binomial-product-comm", "binomialProduct_comm", "Commutativity of the finite convolution",
                "For every pair of real sequences f,g and natural N, binomialProduct(f,g,N) equals binomialProduct(g,f,N). Reflection r maps to N-r preserves the binomial coefficient and interchanges the two factors. Together with productCoeff_eq this makes the smoothed weights symmetric around m/2.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-product-coeff-eq", "productCoeff_eq", "Factorial conversion",
                "For every pair of real sequences f,g and natural N, productCoeff(f,g,N) equals binomialProduct(f,g,N) divided by N factorial. Nat.choose_mul_factorial_mul_factorial supplies the finite coefficient identity; factorials are positive.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-smoothing-minor", "smoothing_minor", "Every smoothed minor is nonnegative",
                "For every real sequence y satisfying IsLogConcave and all natural p,q,N with p <= q+1, productCoeff(r maps to y(p+r),r maps to y(q+2+r),N) <= productCoeff(r maps to y(p+1+r),r maps to y(q+1+r),N). Thus the degree-N coefficient of P(p+1)P(q+1)-P(p)P(q+2) is nonnegative, where P(j) has coefficient y(j+r)/r factorial in degree r. The adjacent-index boundary p=q+1 is equality.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-smoothed-weighting", "smoothed_weighting", "Weighted transformed minors",
                "Let y satisfy IsLogConcave, let A be a real sequence and m a natural number, and put h=floor(m/2). Assume that for all i,j <= h with i < j, A(i)>0 implies A(j)>=0, and that the sum of A(i) for i=0,...,h is nonnegative. Then for every natural degree N, the sum over k=0,...,h of A(k) times productCoeff(r maps to y(2k+r),r maps to y(2(m-k)+r),N) is nonnegative. The sign and total-sum hypotheses concern A alone.", DescribeRole.Theorem),
            Paragraph(Text("Induct simultaneously in the coefficient degree for all derivative-index pairs. The finite Leibniz recurrence makes the next minor the sum of two current minors because the middle products cancel. At the adjacent-index boundary one minor is zero by commutativity. The constant coefficient is the general balancing inequality, obtained by repeated use of the existing balanced_step theorem. Two consecutive balancing steps make P(2k)P(2(m-k)) increase up to the middle; the weighting principle then gives the last theorem. This finite induction proves the same coefficient inequality as the finite Cauchy-Binet argument, without introducing power series or convergence hypotheses.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Smoothing." + name),
            H(title), TheoremStatement(name), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static StatementSource TheoremStatement(string name) =>
        name == "productCoeff" ? StatementSource.FromAuthor(Disp(All("f", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("g", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("N", F.Id("Nat"), Equal(Call("productCoeff", F.Id("f"), F.Id("g"), F.Id("N")), SumRange("r", Add(F.Id("N"), Num(1)), new Formula.Fraction(Multiply(App(F.Id("f"), F.Id("r")), App(F.Id("g"), Subtract(F.Id("N"), F.Id("r")))), Multiply(App(Qualified("Nat", "factorial"), F.Id("r")), App(Qualified("Nat", "factorial"), Subtract(F.Id("N"), F.Id("r")))))))))))) :
        name == "binomialProduct" ? StatementSource.FromAuthor(Disp(All("f", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("g", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("N", F.Id("Nat"), Equal(Call("binomialProduct", F.Id("f"), F.Id("g"), F.Id("N")), SumRange("r", Add(F.Id("N"), Num(1)), Multiply(Multiply(App(Qualified("Nat", "choose"), F.Id("N"), F.Id("r")), App(F.Id("f"), F.Id("r"))), App(F.Id("g"), Subtract(F.Id("N"), F.Id("r"))))))))))) :
        name == "balanced_product" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), Implies(Call("IsLogConcave", F.Id("y")), All("L", F.Id("Nat"), All("R", F.Id("Nat"), All("u", F.Id("Nat"), All("v", F.Id("Nat"), Implies(Le(F.Id("L"), F.Id("u")), Implies(Le(F.Id("L"), F.Id("v")), Implies(Le(F.Id("u"), F.Id("R")), Implies(Le(F.Id("v"), F.Id("R")), Implies(Equal(Add(F.Id("u"), F.Id("v")), Add(F.Id("L"), F.Id("R"))), Le(Multiply(App(F.Id("y"), F.Id("L")), App(F.Id("y"), F.Id("R"))), Multiply(App(F.Id("y"), F.Id("u")), App(F.Id("y"), F.Id("v"))))))))))))))))) :
        name == "binomialProduct_succ" ? StatementSource.FromAuthor(Disp(All("f", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("g", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("N", F.Id("Nat"), Equal(Call("binomialProduct", F.Id("f"), F.Id("g"), Add(F.Id("N"), Num(1))), Add(Call("binomialProduct", LambdaOf("r", App(F.Id("f"), Add(F.Id("r"), Num(1)))), F.Id("g"), F.Id("N")), Call("binomialProduct", F.Id("f"), LambdaOf("r", App(F.Id("g"), Add(F.Id("r"), Num(1)))), F.Id("N"))))))))) :
        name == "binomialProduct_comm" ? StatementSource.FromAuthor(Disp(All("f", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("g", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("N", F.Id("Nat"), Equal(Call("binomialProduct", F.Id("f"), F.Id("g"), F.Id("N")), Call("binomialProduct", F.Id("g"), F.Id("f"), F.Id("N")))))))) :
        name == "productCoeff_eq" ? StatementSource.FromAuthor(Disp(All("f", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("g", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("N", F.Id("Nat"), Equal(Call("productCoeff", F.Id("f"), F.Id("g"), F.Id("N")), new Formula.Fraction(Call("binomialProduct", F.Id("f"), F.Id("g"), F.Id("N")), App(Qualified("Nat", "factorial"), F.Id("N"))))))))) :
        name == "smoothing_minor" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), Implies(Call("IsLogConcave", F.Id("y")), All("p", F.Id("Nat"), All("q", F.Id("Nat"), All("N", F.Id("Nat"), Implies(Le(F.Id("p"), Add(F.Id("q"), Num(1))), Le(Call("productCoeff", LambdaOf("r", App(F.Id("y"), Add(F.Id("p"), F.Id("r")))), LambdaOf("r", App(F.Id("y"), Add(Add(F.Id("q"), Num(2)), F.Id("r")))), F.Id("N")), Call("productCoeff", LambdaOf("r", App(F.Id("y"), Add(Add(F.Id("p"), Num(1)), F.Id("r")))), LambdaOf("r", App(F.Id("y"), Add(Add(F.Id("q"), Num(1)), F.Id("r")))), F.Id("N"))))))))))) :
        name == "smoothed_weighting" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), Implies(Call("IsLogConcave", F.Id("y")), All("A", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("m", F.Id("Nat"), Implies(All("i", F.Id("Nat"), Implies(Le(F.Id("i"), App(Qualified("Nat", "div"), F.Id("m"), Num(2))), All("j", F.Id("Nat"), Implies(Le(F.Id("j"), App(Qualified("Nat", "div"), F.Id("m"), Num(2))), Implies(Lt(F.Id("i"), F.Id("j")), Implies(Lt(Num(0), App(F.Id("A"), F.Id("i"))), Le(Num(0), App(F.Id("A"), F.Id("j"))))))))), Implies(Le(Num(0), SumRange("i", Add(App(Qualified("Nat", "div"), F.Id("m"), Num(2)), Num(1)), App(F.Id("A"), F.Id("i")))), All("N", F.Id("Nat"), Le(Num(0), SumRange("k", Add(App(Qualified("Nat", "div"), F.Id("m"), Num(2)), Num(1)), Multiply(App(F.Id("A"), F.Id("k")), Call("productCoeff", LambdaOf("r", App(F.Id("y"), Add(Multiply(Num(2), F.Id("k")), F.Id("r")))), LambdaOf("r", App(F.Id("y"), Add(Multiply(Num(2), Subtract(F.Id("m"), F.Id("k"))), F.Id("r")))), F.Id("N")))))))))))))) :
        StatementSource.WithoutFormula();

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula LambdaOf(string name, Formula body) =>
        Seq(Operatorname, Grp(F.Id("fun")), Sp, Parenthesized(Seq(F.Id(name), Colon, F.Id("Nat"))), Sp, Mapsto, Sp, body);
    private static Formula SumRange(string name, Formula upper, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(F.Id(name), Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), upper)), Sp, Parenthesized(body));
}
