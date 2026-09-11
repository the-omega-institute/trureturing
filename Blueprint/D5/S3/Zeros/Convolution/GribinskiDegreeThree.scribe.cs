using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Convolution;

internal sealed class GribinskiDegreeThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Convolution/GribinskiDegreeThree.";

    public DocumentDefinition Create()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula d = F.Id("d"), e = F.Id("e"), f = F.Id("f");
        Formula p = F.Id("p"), q = F.Id("q"), k = F.Id("k");
        Formula x = F.Id("x"), u = F.Id("u"), v = F.Id("v");
        Formula r = F.Id("r"), s = F.Id("s"), t = F.Id("t");
        Formula indeterminate = F.Id("X");
        Formula left = Call("R", a, b, c), right = Call("R", d, e, f);
        Formula output = Call("B", Alpha, left, right);
        Formula a1 = Seq(a, Plus, b, Plus, c), b1 = Seq(d, Plus, e, Plus, f);
        Formula a2 = Seq(a, Cdot, Sp, b, Plus, a, Cdot, Sp, c, Plus, b, Cdot, Sp, c);
        Formula b2 = Seq(d, Cdot, Sp, e, Plus, d, Cdot, Sp, f, Plus, e, Cdot, Sp, f);
        Formula sum = Seq(a1, Plus, Paren(b1));
        Formula second = Seq(a2, Plus, Paren(b2), Plus,
            Kappa, Paren(Alpha), Cdot, Paren(a1), Cdot, Paren(b1));
        Formula third = Seq(a, Cdot, Sp, b, Cdot, Sp, c, Plus, d, Cdot, Sp, e, Cdot, Sp, f, Plus,
            Rho, Paren(Alpha), Cdot,
            Paren(Seq(Paren(a1), Cdot, Paren(b2), Plus, Paren(a2), Cdot, Paren(b1))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The degree-three generalized rectangular convolution preserves nonnegative "
                + "real roots for every real alpha greater than minus one.",
            H("Gribinski Convolution in Degree Three"),
            Blocks(
                Paragraph(DefinitionDsl.Text(
                    "This is the fixed degree-three development. The coefficient operation "
                        + "is defined for arbitrary real polynomials before specialization "
                        + "to two root triples. The displayed statements use E, W, N, Q, B, "
                        + "R and Delta for the definitions below, and C for the embedding "
                        + "of a real constant into a polynomial.")),
                Describe.Lean(
                    DescribeId.Create("elementary-coefficient"),
                    DeclarationHandle.Create(Prefix + "elementaryCoeff"),
                    H("Signed Coefficients"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For a real polynomial p and natural number k, E(p,k) is "
                            + "elementaryCoeff p k: (-1)^k times the coefficient of "
                            + "X^(3-k) in p. The subtraction 3-k is natural subtraction."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("weight"),
                    DeclarationHandle.Create(Prefix + "weight"),
                    H("Product Prefactor"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha and natural k, W(alpha,k) is weight alpha k: "
                            + "the product of the kth descending Pochhammer polynomial "
                            + "evaluated at 3 and the same polynomial evaluated at 3+alpha."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("normalized-coefficient"),
                    DeclarationHandle.Create(Prefix + "normalizedCoeff"),
                    H("Normalized Coefficients"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha, real polynomial p and natural k, N(alpha,p,k) "
                            + "is normalizedCoeff alpha p k, namely E(p,k)/W(alpha,k). "
                            + "This uses Lean's total real division."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("coefficient-convolution"),
                    DeclarationHandle.Create(Prefix + "convolutionCoeff"),
                    H("Coefficient Convolution"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha, real polynomials p,q and natural k, Q(alpha,p,q,k) "
                            + "is convolutionCoeff alpha p q k: W(alpha,k) times the sum "
                            + "of N(alpha,p,i)*N(alpha,q,k-i) over i in Finset.range(k+1)."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("polynomial-convolution"),
                    DeclarationHandle.Create(Prefix + "boxplus3"),
                    H("Polynomial Reconstruction"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha and real polynomials p,q, B(alpha,p,q) denotes "
                            + "boxplus3 alpha p q. It is C(Q(alpha,p,q,0))*X^3 "
                            + "- C(Q(alpha,p,q,1))*X^2 + C(Q(alpha,p,q,2))*X "
                            + "- C(Q(alpha,p,q,3))."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("root-triple"),
                    DeclarationHandle.Create(Prefix + "rootTriple"),
                    H("Three Linear Factors"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real a,b,c, R(a,b,c) is rootTriple a b c, the real "
                            + "polynomial (X-C(a))*(X-C(b))*(X-C(c))."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("definition-consistency"),
                    DeclarationHandle.Create(Prefix + "definition_consistency"),
                    H("All Four Defining Coefficients"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, Alpha, InMacro, Reals, Comma, Sp,
                        Forall, Sp, p, Comma, q, InMacro, Reals,
                        OpenBracket, indeterminate, CloseBracket, Comma, Sp,
                        Forall, Sp, k, InMacro, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
                        k, Le, D(3), Sp, Implies, Sp,
                        Call("E", Call("B", Alpha, p, q), k), Eq, Call("Q", Alpha, p, q, k)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For every real alpha, real polynomials p,q and natural k with "
                            + "k<=3, E(B(alpha,p,q),k)=Q(alpha,p,q,k). This includes "
                            + "k=0,1,2,3 and imposes no restriction on alpha."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("kappa"),
                    DeclarationHandle.Create(Prefix + "kappa"),
                    H("Second-Coefficient Cross Weight"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha, kappa(alpha)=2*(alpha+2)/(3*(alpha+3))."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("rho"),
                    DeclarationHandle.Create(Prefix + "rho"),
                    H("Third-Coefficient Cross Weight"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha, rho(alpha)=(alpha+1)/(3*(alpha+3))."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("convolution-coefficients"),
                    DeclarationHandle.Create(Prefix + "convolution_coefficients"),
                    H("Four Explicit Coefficient Sums"),
                    StatementSource.FromAuthor(Disp(OnCoefficientDomain(Seq(
                        Call("Q", Alpha, left, right, D(0)), Eq, D(1), Sp, Land, Sp,
                        Call("Q", Alpha, left, right, D(1)), Eq, sum, Sp, Land, Sp,
                        Call("Q", Alpha, left, right, D(2)), Eq, second, Sp, Land, Sp,
                        Call("Q", Alpha, left, right, D(3)), Eq, third)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha,a,b,c,d,e,f with alpha different from -1, -2 "
                            + "and -3, all four coefficients of the two root triples satisfy: "
                            + "Q0=1; Q1=a+b+c+(d+e+f); "
                            + "Q2=a*b+a*c+b*c+(d*e+d*f+e*f)+kappa(alpha)*(a+b+c)*(d+e+f); "
                            + "Q3=a*b*c+d*e*f+rho(alpha)*((a+b+c)*(d*e+d*f+e*f) "
                            + "+(a*b+a*c+b*c)*(d+e+f)). Here Qj abbreviates "
                            + "Q(alpha,R(a,b,c),R(d,e,f),j). No root signs are assumed."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("explicit-cubic"),
                    DeclarationHandle.Create(Prefix + "m3_explicit_coefficients"),
                    H("The Explicit Cubic"),
                    StatementSource.FromAuthor(Disp(OnCoefficientDomain(Seq(
                        output, Eq, Pow(indeterminate, 3), Minus,
                        Call("C", sum), Cdot, Sp, Pow(indeterminate, 2), Plus,
                        Call("C", second), Cdot, Sp, indeterminate, Minus, Call("C", third))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha,a,b,c,d,e,f with alpha different from -1, -2 "
                            + "and -3, B(alpha,R(a,b,c),R(d,e,f)) equals "
                            + "X^3-C(a+b+c+(d+e+f))*X^2 "
                            + "+C(a*b+a*c+b*c+(d*e+d*f+e*f) "
                            + "+kappa(alpha)*(a+b+c)*(d+e+f))*X "
                            + "-C(a*b*c+d*e*f+rho(alpha)*((a+b+c)*(d*e+d*f+e*f) "
                            + "+(a*b+a*c+b*c)*(d+e+f)))."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("positive-weights"),
                    DeclarationHandle.Create(Prefix + "weight_pos"),
                    H("Positive Weights"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, Alpha, InMacro, Reals, Comma, Sp,
                        Forall, Sp, k, InMacro, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
                        Paren(Seq(Minus, D(1), Lt, Alpha, Sp, Land, Sp, k, Le, D(3))),
                        Sp, Implies, Sp, D(0), Lt, Call("W", Alpha, k)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha with -1<alpha and every natural k with k<=3, "
                            + "the defining weight W(alpha,k) is strictly positive."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("nonnegative-coefficients"),
                    DeclarationHandle.Create(Prefix + "m3_nonnegative_coefficients"),
                    H("Three Nonnegative Signed Coefficients"),
                    StatementSource.FromAuthor(Disp(OnNonnegativeRoots(Seq(
                        Nonnegative(Call("E", output, D(1))), Sp, Land, Sp,
                        Nonnegative(Call("E", output, D(2))), Sp, Land, Sp,
                        Nonnegative(Call("E", output, D(3))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha,a,b,c,d,e,f with -1<alpha and "
                            + "0<=a, 0<=b, 0<=c, 0<=d, 0<=e, 0<=f, set "
                            + "p=B(alpha,R(a,b,c),R(d,e,f)). The conclusion is the "
                            + "conjunction 0<=E(p,1), 0<=E(p,2) and 0<=E(p,3)."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("discriminant"),
                    DeclarationHandle.Create(Prefix + "discriminant"),
                    H("Signed Cubic Discriminant"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For a real polynomial p, Delta(p) denotes discriminant p. "
                            + "Let S=E(p,1), T=E(p,2) and U=E(p,3). Then this definition "
                            + "is S^2*T^2-4*T^3-4*S^3*U-27*U^2+18*S*T*U."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("ordered-gap-coordinates"),
                    DeclarationHandle.Create(Prefix + "nonnegative_rootTriple_coordinates"),
                    H("Nonnegative Gap Coordinates"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, a, Comma, b, Comma, c, InMacro, Reals, Comma, Sp,
                        Paren(Seq(Nonnegative(a), Sp, Land, Sp, Nonnegative(b), Sp, Land, Sp,
                            Nonnegative(c))), Sp, Implies, Sp,
                        Exists, Sp, x, Comma, u, Comma, v, InMacro, Reals, Comma, Sp,
                        Nonnegative(x), Sp, Land, Sp, Nonnegative(u), Sp, Land, Sp,
                        Nonnegative(v), Sp, Land, Sp, left, Eq,
                        Call("R", x, Seq(x, Plus, u), Seq(x, Plus, u, Plus, v))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real a,b,c with 0<=a, 0<=b and 0<=c, there exist real "
                            + "x,u,v such that 0<=x, 0<=u, 0<=v and "
                            + "R(a,b,c)=R(x,x+u,x+u+v). All three inequalities and the "
                            + "polynomial equality are part of the conclusion."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("nonnegative-discriminant"),
                    DeclarationHandle.Create(Prefix + "m3_discriminant_nonneg"),
                    H("Nonnegative Discriminant on the Full Root Domain"),
                    StatementSource.FromAuthor(Disp(OnNonnegativeRoots(
                        Nonnegative(Call("Delta", output))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha,a,b,c,d,e,f with -1<alpha and "
                            + "0<=a, 0<=b, 0<=c, 0<=d, 0<=e, 0<=f, "
                            + "0<=Delta(B(alpha,R(a,b,c),R(d,e,f)))."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("nonnegative-roots"),
                    DeclarationHandle.Create(Prefix + "m3_nonnegative_roots"),
                    H("Preservation of Nonnegative Real Roots"),
                    StatementSource.FromAuthor(Disp(OnNonnegativeRoots(Seq(
                        Exists, Sp, r, Comma, s, Comma, t, InMacro, Reals, Comma, Sp,
                        Nonnegative(r), Sp, Land, Sp, Nonnegative(s), Sp, Land, Sp,
                        Nonnegative(t), Sp, Land, Sp, output, Eq, Call("R", r, s, t))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(DefinitionDsl.Text(
                        "For real alpha,a,b,c,d,e,f with -1<alpha and "
                            + "0<=a, 0<=b, 0<=c, 0<=d, 0<=e, 0<=f, there exist "
                            + "real r,s,t such that 0<=r, 0<=s, 0<=t and "
                            + "B(alpha,R(a,b,c),R(d,e,f))=R(r,s,t). The conclusion "
                            + "retains all three sign conditions and the full factorization."))),
                    DescribeRole.Theorem))));
    }

    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Paren(Formula formula) => Seq(Open, formula, Close);
    private static Formula Pow(Formula formula, byte exponent) => Seq(formula, Caret, Grp(D(exponent)));
    private static Formula Nonnegative(Formula formula) => Seq(D(0), Le, Sp, formula);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula OnCoefficientDomain(Formula conclusion) => OnRealParameters(Seq(
        Paren(Seq(Alpha, Neq, Minus, D(1), Sp, Land, Sp,
            Alpha, Neq, Minus, D(2), Sp, Land, Sp, Alpha, Neq, Minus, D(3))),
        Sp, Implies, Sp, conclusion));

    private static Formula OnNonnegativeRoots(Formula conclusion) => OnRealParameters(Seq(
        Paren(Seq(Minus, D(1), Lt, Alpha, Sp, Land, Sp,
            Nonnegative(F.Id("a")), Sp, Land, Sp, Nonnegative(F.Id("b")), Sp, Land, Sp,
            Nonnegative(F.Id("c")), Sp, Land, Sp, Nonnegative(F.Id("d")), Sp, Land, Sp,
            Nonnegative(F.Id("e")), Sp, Land, Sp, Nonnegative(F.Id("f")))),
        Sp, Implies, Sp, conclusion));

    private static Formula OnRealParameters(Formula body) => Seq(
        Forall, Sp, Alpha, Comma, F.Id("a"), Comma, F.Id("b"), Comma, F.Id("c"),
        Comma, F.Id("d"), Comma, F.Id("e"), Comma, F.Id("f"), InMacro, Reals, Comma, Sp, body);
}
