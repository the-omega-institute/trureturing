using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangGamma;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired reciprocal-gamma kernels and the two-variable transform.",
        H("Pairing and the transformed Turanian"), Blocks(
            Describe.Lean(DescribeId.Create("karp-zhang-gamma-pair-sum"),
                DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Result.pair_sum"),
                H("Reflection of a finite sum"),
                StatementSource.FromAuthor(Disp(
                    All("f", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")),
                        All("m", F.Id("Nat"),
                            Equal(SumRange("k", Add(F.Id("m"), Num(1)), App(F.Id("f"), F.Id("k"))),
                                SumRange("k", Add(App(Qualified("Nat", "div"), F.Id("m"), Num(2)), Num(1)),
                                    PairConditional(
                                        Lt(Multiply(Num(2), F.Id("k")), F.Id("m")),
                                        Add(App(F.Id("f"), F.Id("k")), App(F.Id("f"), Subtract(F.Id("m"), F.Id("k")))),
                                        App(F.Id("f"), F.Id("k"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any real sequence f and natural m, reflect the strict upper half of the finite interval onto the lower half. Each reflected pair contributes its two values, while an even-degree middle term occurs once. Nat.div is natural division. This identity supplies the finite pairing of scalar kernels and the central-tail decomposition."))),
                DescribeRole.Theorem),
            KernelEntry("karp-zhang-gamma-reciprocal-gamma-sum", "reciprocalGamma_sum", "Closed form for the finite convolution",
                "For positive real b,c and every natural m, the sum over k=0,...,m of 1/[k factorial times (m-k) factorial times Real.Gamma(b+k) times Real.Gamma(c+m-k)] equals the evaluation of ascPochhammer at b+c+m-1 in degree m, divided by m factorial times Real.Gamma(b+m) times Real.Gamma(c+m). This is identity (3.11) of the gamma-series argument. It includes m=0 even when b+c-1 is nonpositive.", DescribeRole.Theorem),
            KernelEntry("karp-zhang-gamma-balanced-shift", "gamma_balanced_shift", "Balancing the Gamma product",
                "For every positive real a and nonnegative real alpha,beta, Real.Gamma(a+alpha) times Real.Gamma(a+beta) is at most Real.Gamma(a) times Real.Gamma(a+alpha+beta). The two interior arguments are complementary convex combinations of the endpoints. Add the two inequalities for log composed with Real.Gamma, then use positivity to exponentiate. If the sum of the shifts is zero the assertion is equality.", DescribeRole.Theorem),
            KernelEntry("karp-zhang-gamma-kernel", "kernel", "Unpaired scalar kernel",
                "For real a,alpha,beta and natural m,k, kernel(a,alpha,beta,m,k) equals 1/[k factorial times (m-k) factorial] times the difference between 1/[Real.Gamma(a+alpha+k)Real.Gamma(a+beta+m-k)] and 1/[Real.Gamma(a+k)Real.Gamma(a+alpha+beta+m-k)]. Natural subtraction is literal; the theorems sum only over k <= m.", DescribeRole.Definition),
            KernelEntry("karp-zhang-gamma-kernel-sum-nonneg", "kernel_sum_nonneg", "Nonnegative total kernel",
                "For every positive real a, nonnegative real alpha,beta and natural m, the sum of kernel(a,alpha,beta,m,k) for k=0,...,m is nonnegative. The convolution formula factors this total as the rising-factorial prefactor divided by m factorial, times the reciprocal-gamma balancing difference at a+m. Jensen's inequality for Real.convexOn_log_Gamma makes that difference nonnegative. At m=0 the rising-factorial prefactor is one; at positive degree its argument is positive.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-paired-kernel", "pairedKernel", "Paired scalar kernel",
                "For real a,alpha,beta and natural m,k, pairedKernel(a,alpha,beta,m,k) is kernel(a,alpha,beta,m,k) plus kernel(a,alpha,beta,m,m-k) when 2k < m, and is kernel(a,alpha,beta,m,k) otherwise. The theorems use only 0 <= k <= floor(m/2); the unique middle term in even degree is counted once.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-paired-kernel-sign", "pairedKernel_sign", "One negative-to-positive sign change",
                "For every positive real a, nonnegative real alpha,beta and natural m, take any natural i,j <= floor(m/2) with i < j. If pairedKernel(a,alpha,beta,m,i) is positive, pairedKernel(a,alpha,beta,m,j) is nonnegative. This is the sign condition needed for the finite weighting principle and includes either shift being zero. The proof propagates a nonpositive four-term bracket backwards in the index, then argues by contradiction against a positive earlier bracket.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-finite-pairing", "finite_pairing", "Finite pairing with symmetric weights",
                "For real a,alpha,beta, natural m and a real sequence W satisfying W(m-k)=W(k) for every k <= m, the sum of kernel(a,alpha,beta,m,k) times W(k) over k=0,...,m equals the sum of pairedKernel(a,alpha,beta,m,k) times W(k) over k=0,...,floor(m/2). Split the full interval into its lower half and strict upper half, and reflect the upper half by k maps to m-k. The strict split ensures that an even-degree middle term occurs once.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-paired-kernel-sum-nonneg", "pairedKernel_sum_nonneg", "Nonnegative total paired kernel",
                "For every positive real a, nonnegative real alpha,beta and natural m, the sum of pairedKernel(a,alpha,beta,m,k) over k=0,...,floor(m/2) is nonnegative. Apply finite_pairing with W identically one and use kernel_sum_nonneg. Positivity of this total is not assumed as an additional hypothesis.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-transform-delta", "transformDelta", "A finite coefficient of the transformed Turanian",
                "For a real sequence y, real a,alpha,beta and natural N,m, transformDelta(y,a,alpha,beta,N,m) is the sum over k=0,...,m of kernel(a,alpha,beta,m,k) times Smoothing.productCoeff(r maps to y(2k+r),r maps to y(2(m-k)+r),N). It is the coefficient of z to degree N and w to degree m in the Turanian of H(a;z,w), where H has coefficient y(2j+r)/(r factorial times j factorial times Real.Gamma(a+j)) in degree (r,j). All sums defining a fixed coefficient are finite.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-two-variable-nonneg", "two_variable_nonneg", "Coefficient form of two_variable_nonneg",
                "For every real sequence y satisfying D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave, every positive real a, all nonnegative real alpha,beta and all natural N,m, transformDelta(y,a,alpha,beta,N,m) is nonnegative. There is no convergence or growth hypothesis. Commutativity of the finite smoothed convolution makes the weights symmetric; finite_pairing then expresses the coefficient in terms of pairedKernel. The one-sign-change theorem and nonnegative total supply the hypotheses of Smoothing.smoothed_weighting.", DescribeRole.Theorem),
            Paragraph(Text("For x=a+k, z=a+m-k and alpha <= beta, let u,v,r,s be the reciprocal Gamma products with first arguments x+alpha, x+beta, x and x+alpha+beta respectively. Gamma balancing gives r <= u <= v. If B=u+v-r-s is nonpositive, then v <= s and r <= s. With S=x+z+alpha+beta and F(t)=(t-1)/(S-t), Gamma recurrence writes the preceding bracket as F(x+alpha)B + v(F(x+beta)-F(x+alpha)) + r(F(x+alpha)-F(x)) - s(F(x+alpha+beta)-F(x+alpha)). The first term is nonpositive, and the rest is at most s times F(x+beta)-F(x)-F(x+alpha+beta)+F(x+alpha), which is nonpositive because F has increasing increments. The increment formula is beta times (S-1) divided by the product of the two positive endpoint denominators. Swapping alpha and beta covers the other shift order.")))));

    private static Formula PairConditional(Formula condition, Formula yes, Formula no) =>
        Seq(Operatorname, Grp(F.Id("if")), Sp, Seq(Open, condition, Close), Sp,
            Operatorname, Grp(F.Id("then")), Sp, Seq(Open, yes, Close), Sp,
            Operatorname, Grp(F.Id("else")), Sp, Seq(Open, no, Close));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Result." + name),
            H(title), TheoremStatement(name), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static StatementSource TheoremStatement(string name) =>
        name == "transformDelta" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), All("a", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), All("N", F.Id("Nat"), All("m", F.Id("Nat"), Equal(Call("transformDelta", F.Id("y"), F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("N"), F.Id("m")), SumRange("k", Add(F.Id("m"), Num(1)), Multiply(Call("kernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("k")), Call("productCoeff", LambdaOf("r", App(F.Id("y"), Add(Multiply(Num(2), F.Id("k")), F.Id("r")))), LambdaOf("r", App(F.Id("y"), Add(Multiply(Num(2), Subtract(F.Id("m"), F.Id("k"))), F.Id("r")))), F.Id("N"))))))))))))) :
        name == "pairedKernel" ? StatementSource.FromAuthor(Disp(All("a", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), All("m", F.Id("Nat"), All("k", F.Id("Nat"), Equal(Call("pairedKernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("k")), Call("ite", Lt(Multiply(Num(2), F.Id("k")), F.Id("m")), Add(Call("kernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("k")), Call("kernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), Subtract(F.Id("m"), F.Id("k")))), Call("kernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("k"))))))))))) :
        name == "pairedKernel_sign" ? StatementSource.FromAuthor(Disp(All("a", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), Implies(Lt(Num(0), F.Id("a")), Implies(Le(Num(0), F.Id("alpha")), Implies(Le(Num(0), F.Id("beta")), All("m", F.Id("Nat"), All("i", F.Id("Nat"), Implies(Le(F.Id("i"), App(Qualified("Nat", "div"), F.Id("m"), Num(2))), All("j", F.Id("Nat"), Implies(Le(F.Id("j"), App(Qualified("Nat", "div"), F.Id("m"), Num(2))), Implies(Lt(F.Id("i"), F.Id("j")), Implies(Lt(Num(0), Call("pairedKernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("i"))), Le(Num(0), Call("pairedKernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("j")))))))))))))))))) :
        name == "finite_pairing" ? StatementSource.FromAuthor(Disp(All("a", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), All("m", F.Id("Nat"), All("W", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), Implies(All("k", F.Id("Nat"), Implies(Le(F.Id("k"), F.Id("m")), Equal(App(F.Id("W"), Subtract(F.Id("m"), F.Id("k"))), App(F.Id("W"), F.Id("k"))))), Equal(SumRange("k", Add(F.Id("m"), Num(1)), Multiply(Call("kernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("k")), App(F.Id("W"), F.Id("k")))), SumRange("k", Add(App(Qualified("Nat", "div"), F.Id("m"), Num(2)), Num(1)), Multiply(Call("pairedKernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("k")), App(F.Id("W"), F.Id("k"))))))))))))) :
        name == "pairedKernel_sum_nonneg" ? StatementSource.FromAuthor(Disp(All("a", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), Implies(Lt(Num(0), F.Id("a")), Implies(Le(Num(0), F.Id("alpha")), Implies(Le(Num(0), F.Id("beta")), All("m", F.Id("Nat"), Le(Num(0), SumRange("k", Add(App(Qualified("Nat", "div"), F.Id("m"), Num(2)), Num(1)), Call("pairedKernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("k"))))))))))))) :
        name == "two_variable_nonneg" ? StatementSource.FromAuthor(Disp(All("y", new Formula.TypeArrow(F.Id("Nat"), F.Id("Real")), Implies(Call("IsLogConcave", F.Id("y")), All("a", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), Implies(Lt(Num(0), F.Id("a")), Implies(Le(Num(0), F.Id("alpha")), Implies(Le(Num(0), F.Id("beta")), All("N", F.Id("Nat"), All("m", F.Id("Nat"), Le(Num(0), Call("transformDelta", F.Id("y"), F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("N"), F.Id("m"))))))))))))))) :
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
    private static Formula SumRange(string name, Formula upper, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(F.Id(name), Sp, InMacro, Sp,
            App(Qualified("Finset", "range"), upper)), Sp, Parenthesized(body));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula LambdaOf(string name, Formula body) =>
        Seq(Operatorname, Grp(F.Id("fun")), Sp, Parenthesized(Seq(F.Id(name), Colon, F.Id("Nat"))), Sp, Mapsto, Sp, body);

    private static DocumentBlock KernelEntry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Result." + name),
            H(title), KernelEntryStatement(name), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static StatementSource KernelEntryStatement(string name) =>
        name == "kernel" ? StatementSource.FromAuthor(Disp(All("a", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), All("m", F.Id("Nat"), All("k", F.Id("Nat"), Equal(Call("kernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("k")), Multiply(new Formula.Fraction(Num(1), Multiply(App(Qualified("Nat", "factorial"), F.Id("k")), App(Qualified("Nat", "factorial"), Subtract(F.Id("m"), F.Id("k"))))), Subtract(new Formula.Fraction(Num(1), Multiply(App(Qualified("Real", "Gamma"), Add(Add(F.Id("a"), F.Id("alpha")), F.Id("k"))), App(Qualified("Real", "Gamma"), Add(Add(F.Id("a"), F.Id("beta")), Parenthesized(Subtract(F.Id("m"), F.Id("k"))))))), new Formula.Fraction(Num(1), Multiply(App(Qualified("Real", "Gamma"), Add(F.Id("a"), F.Id("k"))), App(Qualified("Real", "Gamma"), Add(Add(Add(F.Id("a"), F.Id("alpha")), F.Id("beta")), Parenthesized(Subtract(F.Id("m"), F.Id("k"))))))))))))))))) :
        name == "reciprocalGamma_sum" ? StatementSource.FromAuthor(Disp(All("b", F.Id("Real"), All("c", F.Id("Real"), Implies(Lt(Num(0), F.Id("b")), Implies(Lt(Num(0), F.Id("c")), All("m", F.Id("Nat"), Equal(SumRange("k", Add(F.Id("m"), Num(1)), new Formula.Fraction(Num(1), Multiply(Multiply(Multiply(App(Qualified("Nat", "factorial"), F.Id("k")), App(Qualified("Nat", "factorial"), Subtract(F.Id("m"), F.Id("k")))), App(Qualified("Real", "Gamma"), Add(F.Id("b"), F.Id("k")))), App(Qualified("Real", "Gamma"), Add(F.Id("c"), Parenthesized(Subtract(F.Id("m"), F.Id("k")))))))), new Formula.Fraction(App(Qualified("Polynomial", "eval"), Subtract(Add(Add(F.Id("b"), F.Id("c")), F.Id("m")), Num(1)), Call("ascPochhammer", F.Id("Real"), F.Id("m"))), Multiply(Multiply(App(Qualified("Nat", "factorial"), F.Id("m")), App(Qualified("Real", "Gamma"), Add(F.Id("b"), F.Id("m")))), App(Qualified("Real", "Gamma"), Add(F.Id("c"), F.Id("m"))))))))))))) :
        name == "gamma_balanced_shift" ? StatementSource.FromAuthor(Disp(All("a", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), Implies(Lt(Num(0), F.Id("a")), Implies(Le(Num(0), F.Id("alpha")), Implies(Le(Num(0), F.Id("beta")), Le(Multiply(App(Qualified("Real", "Gamma"), Add(F.Id("a"), F.Id("alpha"))), App(Qualified("Real", "Gamma"), Add(F.Id("a"), F.Id("beta")))), Multiply(App(Qualified("Real", "Gamma"), F.Id("a")), App(Qualified("Real", "Gamma"), Add(Add(F.Id("a"), F.Id("alpha")), F.Id("beta"))))))))))))) :
        name == "kernel_sum_nonneg" ? StatementSource.FromAuthor(Disp(All("a", F.Id("Real"), All("alpha", F.Id("Real"), All("beta", F.Id("Real"), Implies(Lt(Num(0), F.Id("a")), Implies(Le(Num(0), F.Id("alpha")), Implies(Le(Num(0), F.Id("beta")), All("m", F.Id("Nat"), Le(Num(0), SumRange("k", Add(F.Id("m"), Num(1)), Call("kernel", F.Id("a"), F.Id("alpha"), F.Id("beta"), F.Id("m"), F.Id("k"))))))))))))) :
        StatementSource.WithoutFormula();

}
