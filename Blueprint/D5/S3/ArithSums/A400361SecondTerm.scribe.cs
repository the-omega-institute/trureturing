using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class A400361SecondTermDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/A400361SecondTerm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/oeis2026a400361");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact second-order summatory formula for the Pillai minus floor-gcd sequence.",
        H("A400361: the second-order summatory constant"),
        Blocks(
            Paragraph(Text("For positive integers n, let P(n) be the sum of gcd(n,k) over "
                + "1 <= k <= n, and let F(n) be the sum of gcd(n,floor(n/k)) over the same "
                + "range. OEIS A400361 revision 17 conjectures the full second-order "
                + "summatory formula for a(n)=P(n)-F(n). All differences are signed. "
                + "The statement below retains every positive integer index and the "
                + "literal digamma, totient, and zeta-derivative constant.")),
            Node("floorGcd", "The floor-gcd sum", Universal("n", Equal(Call("F", V("n")),
                Sum("k", Call("Icc", D(1), V("n")), Call("gcd", V("n"),
                    Call("natDiv", V("n"), V("k")))))),
                "natDiv is natural-number division, hence floor(n/k) for k>0. "
                + "The range includes both endpoints. The sum is natural-valued.", DescribeRole.Definition),
            Node("a", "The signed source sequence", Universal("n", Equal(Call("a", V("n")),
                Sub(Call("toInt", Call("P", V("n"))), Call("toInt", Call("F", V("n")))))),
                "P is Pillai's gcd-sum function. Symmetry of gcd identifies its "
                + "gcd(k,n) convention with gcd(n,k). Both natural values are embedded "
                + "in the integers before subtraction.", DescribeRole.Definition),
            Node("S", "The real cumulative sum", Universal("N", Equal(Call("S", V("N")),
                Sum("n", Call("Icc", D(1), V("N")), Call("toReal", Call("a", V("n")))))),
                "The signed integer source values are cast to the reals. The sum "
                + "at zero is empty; convergence at infinity retains all positive N.", DescribeRole.Definition),
            Node("realDigamma", "The real digamma function", Universal("x", Equal(
                Call("psi", V("x")), Div(Call("derivGamma", V("x")), Call("Gamma", V("x"))))),
                "On the positive real axis this logarithmic derivative of the real "
                + "Gamma function equals the real restriction of complex digamma. "
                + "All arguments 1+1/d used below are positive.", DescribeRole.Definition),
            Node("coefficientTerm", "The positive-index coefficient summand", Universal("d", Equal(
                Call("b", V("d")), Div(Mul(Call("phi", V("d")),
                    Add(Call("psi", Add(D(1), Div(D(1), V("d")))), V("gamma"))), Pow(V("d"), 2)))),
                "phi is Euler's totient and gamma is the Euler-Mascheroni constant. "
                + "For every d>=1, psi(1+1/d)+gamma is the convergent sum over j>=0 "
                + "of 1/((j+1)*(d*(j+1)+1)). In particular d=1 is included. "
                + "Each b(d) is nonnegative and at most pi^2/(6*d^2), proving "
                + "absolute convergence of the defining series.", DescribeRole.Definition),
            Node("C", "The literal second-order constant", Disp(Equal(V("C"), ConstantFormula())),
                "The infinite series is over every positive d. It is encoded by "
                + "d=j+1 for natural j, with no omitted endpoint. The first part is "
                + "the classical Pillai mean constant; the two remaining parts are "
                + "the exact limiting mean of the floor-gcd sum.", DescribeRole.Definition),
            Node("residual", "The second-order remainder", Universal("N", Equal(
                Call("R", V("N")), Sub(Sub(Call("S", V("N")), MainTerm()),
                    Mul(V("C"), Pow(V("N"), 2))))),
                "R is S(N) minus the displayed leading logarithmic term and C*N^2. "
                + "Division by N^2 tends to zero exactly when R=o(N^2). The "
                + "equivalence uses that N^2 is nonzero for every positive N.", DescribeRole.Definition),
            Node("originalClaim", "The exact unrestricted assertion", ClaimFormula(),
                "The claim conjoins summability of b(j+1) with R(N)=o(N^2) as "
                + "N tends to infinity through all natural numbers. There is no "
                + "subsequence, finite cutoff, arithmetic restriction, or extra hypothesis.", DescribeRole.Definition),
            Node("result", "The full second-order formula", ClaimFormula(),
                "Expand gcd by the sum of totients over common divisors. Writing "
                + "n=d*m and floor(d*m/k)=d*ell gives m=k*ell+r with d*r<k. "
                + "The edge r=0 contributes the ordinary divisor-sum prefix. For r>0, "
                + "k=d*r+j gives the positive lattice triangle (d*ell+1)*r+ell*j<=N/d. "
                + "Its normalized count tends to 1/(2*ell*(d*ell+1)). A summable "
                + "majorant permits passage through both divisor indices. Consequently "
                + "the floor-gcd prefix divided by N^2 tends to pi^2/12 plus half "
                + "the convergent sum of b(d). For the Pillai part, its totient "
                + "divisor formula gives a Mobius convolution of the weighted divisor "
                + "pair count. The exact symmetric hyperbola split at floor(sqrt(N)) "
                + "and the harmonic-number limit give the weighted second term. "
                + "Dominated convergence transfers it through the Mobius convolution. "
                + "The quotient-square defect is at most 2/(N*d), and its tail is at "
                + "most 1/N; multiplication by log(N) therefore leaves a vanishing "
                + "error. Differentiating the actual zeta-Mobius Dirichlet identity "
                + "at two supplies the literal zeta derivative. Subtraction yields "
                + "exactly C and the asserted unrestricted little-o remainder. "
                + "The classical Pillai asymptotic is prior mathematics, attributed "
                + "in oeis2026a400361; its formal derivation is used here as a dependency.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a400361-second-order-pillai-floor-gcd"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a400361-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula ConstantFormula() => Sub(Sub(Mul(Div(D(3), Pow(V("pi"), 2)),
        Sub(Add(Div(Seq(Minus, D(1)), D(2)), Mul(D(2), V("gamma"))),
            Div(Mul(D(6), Call("derivZetaR", D(2))), Pow(V("pi"), 2)))),
        Div(Pow(V("pi"), 2), D(1, 2))), Mul(Div(D(1), D(2)),
            Sum("d", Call("Ici", D(1)), Call("b", V("d")))));
    private static Formula MainTerm() => Mul(Mul(Div(D(3), Pow(V("pi"), 2)),
        Pow(V("N"), 2)), Call("log", V("N")));
    private static Formula ClaimFormula() => Disp(Call("and",
        Call("Summable", Seq(V("j"), Sp, Mapsto, Sp, Call("b", Add(V("j"), D(1))))),
        Call("littleOAtTop", Seq(V("N"), Sp, Mapsto, Sp, Call("R", V("N"))),
            Seq(V("N"), Sp, Mapsto, Sp, Pow(V("N"), 2)))));
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, int n) => new Formula.Power(a, D((byte)n));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Universal(string name, Formula body) => Disp(Seq(Forall, Sp, V(name), Sp, InMacro, Sp, Call(name == "x" ? "Real" : "Nat"), Comma, Sp, body));
    private static Formula Sum(string name, Formula range, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, range)), Sp, Grp(body));
}
