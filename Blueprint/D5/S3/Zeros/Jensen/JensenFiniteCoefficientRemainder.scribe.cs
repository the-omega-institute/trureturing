using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class JensenFiniteCoefficientRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Jensen/JensenFiniteCoefficientRemainder.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Pow(Formula value, Formula power) => Seq(value, Sup, Grp(power));
    private static Formula Fr(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula NatBind(params Formula[] variables) =>
        Seq(Forall, Sp, Seq(variables), InMacro, Sp, Mathbb, Grp(V("N")), Comma, Sp);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite coefficients and an ordered product remainder serve the complete actual-source fixed-window consumer.",
        H("Finite Jensen coefficients and remainder"),
        Blocks(
            Describe.Lean(DescribeId.Create("jensen-falling-real"),
                DeclarationHandle.Create(Prefix + "fallingReal"), H("Natural falling factorial"),
                StatementSource.FromAuthor(Disp(Seq(NatBind(V("j"), Comma, V("k")),
                    Call(V("fallingReal"), V("j"), V("k")), Eq,
                    Call(V("descFactorial"), V("j"), V("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural falling factorial is coerced to Real. It is one at k=0 and exactly zero when k>j."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jensen-elementary-symmetric"),
                DeclarationHandle.Create(Prefix + "elementarySymmetric"), H("Finite subset coefficients"),
                StatementSource.FromAuthor(Disp(Seq(NatBind(V("r"), Comma, V("j")),
                    Call(V("e"), V("r"), V("j")), Eq, Sum, Underscore,
                    Grp(Seq(V("S"), Subseteq, Sp, Call(V("range"), V("j")), Comma,
                        Call(V("card"), V("S")), Eq, V("r"))), Sp,
                    Prod, Underscore, Grp(Seq(V("i"), InMacro, Sp, V("S"))), Sp, V("i")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("e(r,j) denotes elementarySymmetric r j. All finite subsets are retained, including those whose product contains zero; e(0,j)=1. Splitting by the new index proves e(r+1,j+1)=e(r+1,j)+j*e(r,j). The equivalent nonnegative product estimate follows by simultaneous induction from this split and Mathlib pow_add_mul_le_add_pow: r!*e(r,j)<=S(j)^r with S(j)=sum(i<j)i<=j^2/2. Thus e(r,j)<=j^(2r)/(2^r*r!), for every r,j."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jensen-correction-coefficient"),
                DeclarationHandle.Create(Prefix + "correctionCoeff"), H("Finite correction recurrence"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Call(V("c"), D(0), D(0)), Eq, D(1), Comma, Sp,
                        NatBind(V("k")), Call(V("c"), D(0), Seq(V("k"), Plus, D(1))), Eq, D(0)),
                    Seq(NatBind(V("r")), Call(V("c"), Seq(V("r"), Plus, D(1)), D(0)), Eq, D(0), Comma, Sp,
                        Call(V("c"), Seq(V("r"), Plus, D(1)), D(1)), Eq, D(0)),
                    Seq(NatBind(V("r"), Comma, V("k")),
                        Call(V("c"), Seq(V("r"), Plus, D(1)), Seq(V("k"), Plus, D(2))), Eq,
                        Fr(Seq(Open, V("k"), Plus, D(1), Close, Call(V("c"), V("r"), Seq(V("k"), Plus, D(1))),
                            Plus, Call(V("c"), V("r"), V("k"))), Seq(V("k"), Plus, D(2))))
                ]))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("c denotes correctionCoeff. Its nonnegative support is (r,k)=(0,0), or r+1<=k<=2r. The above-support coefficient is zero, so the top recurrence gives c(r,2r)=1/(2^r*r!). No permutation-cardinality assertion is used."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jensen-correction-sum"),
                DeclarationHandle.Create(Prefix + "correctionSum"), H("Falling-factorial construction"),
                StatementSource.FromAuthor(Disp(Seq(NatBind(V("r"), Comma, V("j")),
                    Call(V("correctionSum"), V("r"), V("j")), Eq,
                    Sum, Underscore, Grp(Seq(D(0), Le, V("k"), Le, D(2), V("r"))), Sp,
                    Call(V("c"), V("r"), V("k")), Call(V("fallingReal"), V("j"), V("k"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The endpoint-zero index shift proves correctionSum(r+1,j+1)-correctionSum(r+1,j)=j*correctionSum(r,j). Simultaneous induction on j for all r identifies correctionSum(r,j)=e(r,j), including r=0 and orders above the subset degree. These private suppliers are opened by ActualSourceJensenFixedWindow on its live correction and scaled-estimate paths."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jensen-bonferroni-residual"),
                DeclarationHandle.Create(Prefix + "bonferroniResidual"), H("Exact finite remainder"),
                StatementSource.FromAuthor(Disp(Seq(NatBind(V("n"), Comma, V("K"), Comma, V("j")),
                    Call(V("rho"), V("n"), V("K"), V("j")), Eq,
                    Fr(Call(V("descFactorial"), V("n"), V("j")), Pow(V("n"), V("j"))), Minus,
                    Sum, Underscore, Grp(Seq(D(0), Le, V("r"), Le, V("K"))), Sp,
                    Fr(Seq(Pow(Seq(Open, Minus, D(1), Close), V("r")), Call(V("e"), V("r"), V("j"))), Pow(V("n"), V("r")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("rho is bonferroniResidual, with the original quotient and all K+1 truncation coefficients. Pochhammer evaluation identifies the quotient with the complete product of (1-i/n) for i<j.")),
                    Paragraph(Text("Define the private ordered remainder T(0,j)=product(i<j)(1-i/n) and T(k+1,j)=sum(i<j)(i/n)*T(k,i). Every recursive selection decreases the next index and retains the full product below the smallest selected index. Iterating Mathlib prod_one_sub_ordered proves T(k,j)=e(k,j)/n^k-T(k+1,j), and the exact signed residual is (-1)^(K+1)*T(K+1,j). For j<=n all retained factors lie in [0,1], giving 0<=T(k,j)<=e(k,j)/n^k.")),
                    Paragraph(Text("For j>n the natural falling factorial is exactly zero. With x=j^2/n>=1, the absolute truncation is bounded by sum(r<=K)x^r/(2^r*r!)<=x^(K+1)*sum(r<=K)2^(-r)<=2*x^(K+1). The two cases prove |rho(n,K,j)|<=2*j^(2K+2)/n^(K+1) for every n>=1 and every natural K,j, retaining j=0, K=0 and zero factors.")),
                    Paragraph(Text("For a:Nat->Complex, b,K natural and R>=1, the differentiated coefficient majorant is sum_j norm(a(j))*|rho(n,K,j)|*descFactorial(j,b)*R^(j-b)<=2/n^(K+1)*sum_j norm(a(j))*j^(2K+2+b)*R^j. Its sole summability premise is that the series on the right is summable. Terms j<b vanish exactly, while descFactorial(j,b)<=j^b and R^(j-b)<=R^j provide the pointwise domination and summability of the left series.")),
                    Paragraph(Text("This module is a consumed finite intermediate. It does not prove the complete fixed-window theorem, analytic differentiation, local node construction, compact-window exhaustion, or RH; those remain obligations of the unchanged full consumer."))),
                DescribeRole.Definition))));
}
