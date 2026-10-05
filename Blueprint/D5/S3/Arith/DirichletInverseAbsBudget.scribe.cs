using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class DirichletInverseAbsBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An absolute head gap gives absolute summability and a quantitative norm bound for a Dirichlet inverse.",
        H("Absolute Budget for Dirichlet Inversion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dirichlet-inverse-absolute-budget"),
                DeclarationHandle.Create("D5/S3/Arith/DirichletInverseAbsBudget.dirichletInverse_absolute_budget"),
                H("A finite tail budget controls the entire inverse"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/ArithSums/glocknerlucht2011weightedinversion")),
                Blocks(
                    Paragraph(Text("Let b and g be real ArithmeticFunction values and T a real number. "
                        + "This carrier includes b(0)=g(0)=0. Multiplication means Dirichlet convolution, "
                        + "with unit delta at index one. Assume b*g=1, assume every finite sum of "
                        + "|b(d)| over 1<d<=N is at most T, and assume T<|b(1)|. "
                        + "Then the absolute coefficients of g are summable over all natural indices, "
                        + "including the zero coefficient, and their sum is at most 1/(|b(1)|-T). "
                        + "The first coefficient may be negative. The empty tail at N=0 is included; "
                        + "it forces T>=0 and the strict gap makes the denominator positive.")),
                    Paragraph(Text("Write r=b-b(1) delta, B(d)=|r(d)|, G(d)=|g(d)|, "
                        + "and S_N=sum over 0<n<=N of |g(n)|. The inverse identity and the "
                        + "coefficient triangle inequality give |b(1)| |g(n)|<=delta(n)+(B*G)(n). "
                        + "The existing summatory convolution formula expresses the finite "
                        + "convolution sum as sum B(d) S_floor(N/d). Nonnegative coefficients "
                        + "and floor(N/d)<=N bound it by T S_N. Thus "
                        + "(|b(1)|-T) S_N<=1 for every finite cutoff, with cutoff zero handled "
                        + "by its empty sum. Since g(0)=0, the same bound controls all range sums. "
                        + "The existing nonnegative real-series APIs give summability and the total sum bound.")),
                    Paragraph(Text("This is the classical l1 Dirichlet convolution inversion estimate. "
                        + "Glöckner and Lucht describe the absolute coefficient convolution Banach "
                        + "algebra on page 1, its ordinary Dirichlet series model on page 3, and the "
                        + "standard norm perturbation invertibility principle in Theorem 2(a), "
                        + "page 4. The quantitative estimate is the elementary Neumann-series "
                        + "consequence obtained by normalizing the head. The Lean proof uses finite "
                        + "absorption and does not assume a global norm or summability for the unknown inverse. "
                        + "The cited general Wiener theorem has stronger spectral hypotheses than "
                        + "a pointwise nonvanishing claim. This theorem supplies an inverse coefficient "
                        + "budget; it establishes no Riemann hypothesis or originality claim."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var b = F.Id("b"); var g = F.Id("g"); var t = F.Id("T");
        var n = F.Id("N"); var d = F.Id("d"); var k = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula abs(Formula x) => new Formula.Absolute(x);
        Formula tail = Seq(Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            new Formula.Subscript(Sum, Seq(D(1), Lt, Sp, d, Le, Sp, n)),
            abs(Call("b", d)), Le, Sp, t);
        Formula total = Seq(new Formula.Subscript(Sum, Seq(k, InMacro, Sp, naturals)),
            abs(Call("g", k)));
        Formula absSequence = Seq(k, Mapsto, Sp, abs(Call("g", k)));
        return Disp(Seq(Forall, Sp, b, Comma, g, InMacro, Sp,
            Call("ArithmeticFunction", reals), Comma, Sp,
            Forall, Sp, t, InMacro, Sp, reals, Comma, Sp,
            Open, tail, Close, Land, Sp, t, Lt, Sp, abs(Call("b", D(1))), Land, Sp,
            Call("DirichletConvolution", b, g), Eq, Sp,
            new Formula.Subscript(F.Id("delta"), D(1)),
            Rightarrow, Sp, Call("Summable", absSequence), Land, Sp,
            total, Le, Sp, new Formula.Fraction(D(1), Seq(abs(Call("b", D(1))), Minus, t))));
    }
}
