using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.PowerSeries;

internal sealed class BalaBilateralLogDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/PowerSeries/BalaBilateralLog.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/AnalyticClosure/bala2025bilaterallog");
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Pair(Formula b) => All("x", C, All("a", C, All("k", N, b)));
    private static Formula X => F.Id("x");
    private static Formula A => F.Id("a");
    private static Formula K => F.Id("k");
    private static Formula M => Add(K, D(1));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("bilateral-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two variable-exponent tails are absolutely convergent throughout the separate complex unit disks and their sum is the principal negative logarithm.",
        H("Bala's bilateral logarithm identity"), Blocks(
            Definition("positive", "The positive source tail", Pair(Equal(Call("positive", X, A, K),
                Div(Pow(Sub(X, Pow(A, M)), M), M))),
                "The natural index k starts at zero; the source index is m=k+1. Both parameters are arbitrary complex numbers. This polynomial expression and its positive integer divisor define p_m independently of a proposed sum."),
            Definition("negative", "The regular negative tail", Pair(Equal(Call("negative", X, A, K),
                Div(Mul(Pow(Sub(D(0), D(1)), Add(K, D(2))), Pow(A, Mul(M, M))),
                    Mul(M, Pow(Sub(D(1), Mul(X, Pow(A, M))), M))))),
                "This is q_m=(-1)^(m+1)a^(m*m)/(m(1-x*a^m)^m), with m=k+1. The theorem establishes nonzero denominators on the separate unit disks. This regular expression is defined at a=0; it is distinct from the raw negative-power expression."),
            Definition("regularSum", "The sum of the two independently defined tails",
                All("x", C, All("a", C, Equal(Call("regularSum", X, A),
                    Add(Call("tsum", Call("positive", X, A)), Call("tsum", Call("negative", X, A)))))),
                "F(x,a) is the unordered natural sum of p plus the unordered natural sum of q. Separate absolute convergence is a conclusion. The definition does not use a logarithm, a cancellation premise or an assumed convergence proof."),
            Definition("raw", "The ordinary complex bilateral family",
                All("x", C, All("a", Call("Nonzero", C), All("n", Call("Nonzero", Z),
                    Equal(Call("raw", X, A, F.Id("n")),
                        Div(Pow(Sub(X, Pow(A, F.Id("n"))), F.Id("n")), F.Id("n")))))),
                "Nonzero(C) means the subtype of complex parameters a!=0, and Nonzero(Z) means integers n!=0. All powers displayed here are ordinary integer powers. There is no raw family at parameter zero and no raw term at integer index zero."),
            Definition("realRaw", "The original real source family",
                All("x", R, All("a", Call("Nonzero", R), All("n", Call("Nonzero", Z),
                    Equal(Call("realRaw", X, A, F.Id("n")),
                        Div(Pow(Sub(X, Pow(A, F.Id("n"))), F.Id("n")), F.Id("n")))))),
                "The real source family uses real arithmetic and ordinary integer powers, with nonzero real a and nonzero integer n. Complexification preserves each term."),
            Describe.Lean(DescribeId.Create("bilateral-full-event"),
                DeclarationHandle.Create(Prefix + "full_event"), H("The complete full-domain identity and extension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("For every complex x,a with norm(x)<1 and norm(a)<1 separately, the norm series of positive(x,a,k) and negative(x,a,k) are summable, and F(x,a)=-Complex.log(1-x). Complex.log is Mathlib's principal complex logarithm. For every natural k, k+1 and 1-x*a^(k+1) are nonzero. Moreover Re(1-x)>0. No combined-norm, sign, diagonal or smaller-disk condition is imposed.")),
                    Paragraph(Text("For every such x and every nonzero a in its unit disk, and every integer n!=0, a^n and the complex integer divisor n are nonzero; if n<0, x-a^n is nonzero as well. For every k>=0, raw(x,a,k+1)=positive(x,a,k) and raw(x,a,-(k+1))=negative(x,a,k). The norm family over all nonzero integers is summable. HasSum of that unordered family has value F, its tsum equals F, and the sum of its separately indexed positive and negative tails equals F. The finite symmetric sums over k=0,...,N-1 of raw(k+1)+raw(-(k+1)) tend to F as N tends to infinity. These are the source truncations over -N,...,-1,1,...,N.")),
                    Paragraph(Text("For every real x and nonzero real a with abs(x)<1 and abs(a)<1, realRaw is absolutely summable and HasSum realRaw (-Real.log(1-x)). In particular negative x and negative a are included. Since 1-x>0, Complex.ofReal_log identifies the principal complex value with the embedded real logarithm. This is an identity of the original real series, not only an identity of a complex formula.")),
                    Paragraph(Text("For each fixed complex x in its unit disk, positive(x,0,k)=x^(k+1)/(k+1) and negative(x,0,k)=0 for every k. The independently defined F(x,a) is continuous at a=0. If any H:C->C is continuous at zero within the open a-disk and equals the punctured raw unordered sum at every nonzero a in that disk, then H=F throughout that disk. Values of H outside the disk are unconstrained. The proof establishes continuity and uniqueness separately; it assigns no value to the raw expression at a=0.")),
                    Paragraph(Text("Put c(n,m)=0 for m=0 and c(n,m)=(-a^n)^m*x^(n-m)*choose(n,m)/n otherwise. Its finite row of norms is bounded by (norm(x)+norm(a)^n)^n. Choose rho=(1+norm(x))/2<1; eventually norm(a)^n<rho-norm(x), so this row majorant is dominated by rho^n. This proves joint absolute summability before any change of order. The finite binomial theorem gives the row sum ((x-a^n)^n-x^n)/n. The negative-binomial HasSum supplier at x*a^(k+1), whose norm is less than one, gives the column sum -q_(k+1). Absolute Fubini cancellation leaves sum x^n/n, identified by Complex.hasSum_taylorSeries_neg_log. The raw bridges use nonzero ordinary powers. Uniqueness uses the nontrivial punctured neighborhood filter at zero.")),
                    Paragraph(Text("The fixed source comments in A292179 and A292178 pose one question. The paired entries do not represent two independent settlements. The cited source note gives the exact quotations, parameter interpretation and bounded literature limitations; no global novelty or priority claim is made."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bala-a292179-a292178-bilateral-logarithm"), ResolutionKind.Proved)))));
}
