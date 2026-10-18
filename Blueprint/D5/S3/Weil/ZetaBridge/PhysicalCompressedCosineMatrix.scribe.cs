using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class PhysicalCompressedCosineMatrixDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/PhysicalCompressedCosineMatrix.";

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    private static Formula Mul(Formula x, Formula y) => Call("mul", x, y);
    private static Formula Add(Formula x, Formula y) => Call("add", x, y);
    private static Formula Sub(Formula x, Formula y) => Call("sub", x, y);
    private static Formula Div(Formula x, Formula y) => Call("div", x, y);

    public DocumentDefinition Create()
    {
        Formula a = F.Id("a"), s = F.Id("s"), n = F.Id("n"), m = F.Id("m");
        Formula A = F.Id("A"), v = F.Id("v"), M = F.Id("M"), x = F.Id("x");
        Formula f = F.Id("f"), y = F.Id("y"), r = F.Id("r"), u = F.Id("u"), frequencyV = F.Id("v");
        Formula window = Call("window", a), overlap = Call("overlap", a, s);
        Formula wn = Call("omega", a, n), wm = Call("omega", a, m);
        Formula absS = Call("abs", s), twoA = Mul(D(2), a);
        Formula width = Div(Sub(twoA, absS), D(2));
        Formula channels = Add(
            Mul(Call("cos", Div(Mul(Add(wn, wm), absS), D(2))), Call("S", width, Sub(wn, wm))),
            Mul(Call("cos", Div(Mul(Sub(wn, wm), absS), D(2))), Call("S", width, Add(wn, wm))));
        Formula profile = Call("profile", a, A, v);
        Formula profileX = Call("apply", profile, x);
        Formula cutoff = Call("primeCutoff", a);
        Formula coeff = Mul(Call("conj", Call("apply", v, n)), Call("apply", v, m));
        Formula logR = Call("log", r);
        Formula complexSum = Mul(D(2), Call("SumIcc", r, D(1), cutoff,
            Mul(Call("ofReal", Call("primeWeight", r)),
                Call("SumDouble", n, m, A, Mul(coeff,
                    Call("ofReal", Call("matrix", a, n, m, logR)))))));
        Formula realSum = Mul(D(2), Call("SumIcc", r, D(1), cutoff,
            Mul(Call("primeWeight", r), Call("SumDouble", n, m, A,
                Mul(Call("Re", coeff), Call("matrix", a, n, m, logR))))));
        Formula assumptions = Call("And", Call("LessThan", D(0), a), Call("LessEqual", cutoff, M));
        Formula zeroProfile = Call("zeroExtension", a, profile);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact physical Ioc zero-extension cosine compression and the finite complex prime-power quadratic form.",
            H("Physical Compressed Cosine Matrix"),
            Blocks(
                Paragraph(Text(
                    "The physical window is Ioc(-a,a]. Every translated factor is zero-extended "
                    + "before evaluation, with an outer compression to the same window. "
                    + "The formulas below describe applications of interval integration, cosine "
                    + "product-to-sum, indicator support geometry and finite integral linearity. "
                    + "No literature novelty, signed positivity or Riemann-hypothesis conclusion is asserted.")),
                Describe.Lean(DescribeId.Create("window"),
                    DeclarationHandle.Create(Owner + "window"), H("Physical window"),
                    StatementSource.FromAuthor(Disp(Seq(window, Eq, Call("Ioc", Seq(Minus, a), a)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The lower endpoint is excluded and the upper endpoint is included."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("zero-extension"),
                    DeclarationHandle.Create(Owner + "zeroExtension"), H("Original zero extension"),
                    StatementSource.FromAuthor(Disp(Seq(Call("zeroExtension", a, f, x), Eq,
                        Call("Indicator", window, f, x)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Both sides are evaluated at x."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("compression"),
                    DeclarationHandle.Create(Owner + "compression"), H("Compressed translation"),
                    StatementSource.FromAuthor(Disp(Seq(Call("compression", a, s, f, x), Eq,
                        Call("zeroExtension", a, Call("lambda", y,
                            Call("zeroExtension", a, f, Add(y, s))), x)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The inner zero extension is evaluated at y+s; the outer one is evaluated at x."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("overlap"),
                    DeclarationHandle.Create(Owner + "overlap"), H("Exact overlap"),
                    StatementSource.FromAuthor(Disp(Seq(overlap, Eq,
                        Call("Ioc", Call("max", Seq(Minus, a), Sub(Seq(Minus, a), s)),
                            Call("min", a, Sub(a, s)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The overlap is empty at either touching boundary and beyond support."))),
                    DescribeRole.Definition),
                Paragraph(Text(
                    "For any RCLike scalar field, pairing(a,s,f,g)=integral over the real line of "
                    + "f(x)*compression(a,s,g)(x). Indicator restriction gives its integral over "
                    + "Ioc(-a,a] and pairing_overlap gives the set integral over overlap(a,s) of "
                    + "f(x)*g(x+s). Neither identity needs continuity. For 0<=s<=2a this is the "
                    + "oriented interval integral from -a to a-s. For -(2a)<=s<=0 it is the "
                    + "oriented interval integral from -a-s to a. It is zero when 2a<=s or "
                    + "s<=-(2a), including equality. If s>=0 and f(-x)=f(x), g(-x)=g(x) for "
                    + "every x, reflection gives pairing(a,-s,f,g)=pairing(a,s,f,g). "
                    + "Reflection identifies integrals, without identifying the endpoint values of reflected Ioc indicators.")),
                Describe.Lean(DescribeId.Create("cosine-product"),
                    DeclarationHandle.Create(Owner + "integral_cos_product_overlap"), H("Complete oriented cosine integral"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("IntervalIntegral", x, Seq(Minus, a), Sub(a, s),
                            Mul(Call("cos", Mul(u, x)), Call("cos", Mul(frequencyV, Add(x, s))))), Eq,
                        Add(Mul(Call("cos", Div(Mul(Add(u, frequencyV), s), D(2))),
                                Call("S", Div(Sub(twoA, s), D(2)), Sub(u, frequencyV))),
                            Mul(Call("cos", Div(Mul(Sub(u, frequencyV), s), D(2))),
                                Call("S", Div(Sub(twoA, s), D(2)), Add(u, frequencyV))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "All a,s,u,v are arbitrary real numbers. "
                        + "IntervalIntegral means the ORIENTED Lebesgue interval integral, not an Icc set integral; "
                        + "reversed endpoints retain their sign. S(H,r)=H*sinc(r*H), with S(H,0)=H, "
                        + "S(0,r)=0 and S(H,-r)=S(H,r). The midpoint substitution y=x+s/2 and "
                        + "two_mul_cos_mul_cos give both channels. The cases u-v=0, u+v=0 and H=0 are included."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("matrix"),
                    DeclarationHandle.Create(Owner + "matrix"), H("Physical compressed matrix"),
                    StatementSource.FromAuthor(Disp(Seq(Call("matrix", a, n, m, s), Eq,
                        Call("If", Call("LessEqual", absS, twoA),
                            Mul(Mul(Call("amplitude", a, n), Call("amplitude", a, m)), channels), D(0))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "omega(a,n)=2*pi*n/(2*a); amplitude(a,0)=1/sqrt(2*a), and "
                        + "amplitude(a,n)=sqrt(2/(2*a)) for n!=0. mode(a,n,x) is amplitude(a,n)*cos(omega(a,n)*x). "
                        + "matrixEntry(a,n,m,s)=pairing(a,s,mode(a,n),mode(a,m)). Under 0<a, "
                        + "matrixEntry_eq_matrix identifies this pairing with the displayed matrix for "
                        + "every real s and every natural n,m, including both zero modes and both resonances. "
                        + "At |s|=2a both S widths vanish, so the support branch includes its zero boundary."))),
                    DescribeRole.Definition),
                Paragraph(Text(
                    "For the following normalized consequences assume a>0, and put H=(2*a-s)/2 and omega_n=omega(a,n). "
                    + "For 0<=s<=2a the zero row is 2*amplitude(a,0)*amplitude(a,m)*cos(omega_m*s/2)*S(H,omega_m), "
                    + "including m=0. In particular the zero-zero entry is 1-s/(2*a). For n>0 and 0<=s<=2a, "
                    + "the diagonal is (1-s/(2*a))*cos(omega_n*s)-sin(omega_n*s)/((2*a)*omega_n), "
                    + "with its negative sine term. For distinct n,m and 0<=s<=2a, both omega_n-omega_m and "
                    + "omega_n+omega_m are nonzero, so replacing each S(H,r) in the two-channel formula "
                    + "by sin(r*H)/r gives the off-diagonal formula, including a single zero mode. "
                    + "For all signed shifts the matrix is even in s and symmetric in n,m; "
                    + "at s=0 it is 1 when n=m and 0 otherwise. These are consequences of the same formula, "
                    + "the amplitude squares and integer sine identities, with no additional orthogonality assumption.")),
                Describe.Lean(DescribeId.Create("profile-pairing"),
                    DeclarationHandle.Create(Owner + "profile_pairing"), H("Finite complex profile expansion"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("pairing", a, s, Call("lambda", x, Call("conj", profileX)), profile), Eq,
                        Call("SumDouble", n, m, A, Mul(coeff, Call("ofReal", Call("matrixEntry", a, n, m, s))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For arbitrary real a,s, finite A of natural modes and complex v, "
                        + "profile(a,A,v,x)=sum over n in A of v(n)*(mode(a,n,x):complex). "
                        + "Every conjugated mixed term remains in the double sum. Under a>0, matrix symmetry "
                        + "also proves that this correlation is real; no real-coefficient restriction is imposed."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("prime-action"),
                    DeclarationHandle.Create(Owner + "primeAction"), H("Original finite prime-power action"),
                    StatementSource.FromAuthor(Disp(Seq(Call("primeAction", a, M, f, x), Eq,
                        Call("SumIcc", r, D(1), M, Mul(Call("ofReal", Call("primeWeight", r)),
                            Add(Call("compression", a, logR, f, x),
                                Call("compression", a, Seq(Minus, logR), f, x))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "primeWeight(r)=vonMangoldt(r)/sqrt(r), from PrimeJumpDecomposition. "
                        + "All prime powers remain, and the r=1 weight is zero by vonMangoldt_apply_one. "
                        + "For x in Ioc(-a,a], this action equals the existing primeSymmetric(a,M,zeroExtension(a,f),x). "
                        + "primeCutoff(a)=floor(exp(2*a)). For M>=primeCutoff(a), primeAction_cutoff removes "
                        + "only shifts beyond support; a shift equal to 2a also has empty Ioc overlap."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("finite-prime-quadratic"),
                    DeclarationHandle.Create(Owner + "finite_prime_quadratic"), H("Exact finite complex identity"),
                    StatementSource.FromAuthor(Disp(Call("Implies", assumptions, Seq(
                        Call("IntegralWindow", x, window, Mul(Call("conj", profileX),
                            Call("primeAction", a, M, profile, x))), Eq, complexSum)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The hypotheses are ha:0<a and hM:primeCutoff(a)<=M. The set A is any finite set of "
                        + "natural modes and v is any complex coefficient family. Even reflection produces "
                        + "factor two from the two separately compressed signed shifts. Taking the real "
                        + "part retains Re(conj(v(n))*v(m)) for every pair. Under the same ha and hM, "
                        + "finite_prime_quadratic_real identifies the full complex integral with the real scalar expression."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("signed-weil-prime-quadratic"),
                    DeclarationHandle.Create(Owner + "finite_weil_prime_quadratic"), H("Original negative Weil prime component"),
                    StatementSource.FromAuthor(Disp(Call("Implies", assumptions, Seq(
                        Call("IntegralWindow", x, window, Mul(Call("conj", Call("apply", zeroProfile, x)),
                            Seq(Minus, Call("primeSymmetric", a, M, zeroProfile, x)))), Eq,
                        Seq(Minus, Call("ofReal", realSum)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Here again ha:0<a and hM:primeCutoff(a)<=M are required, with arbitrary finite A "
                        + "and complex v. The negative sign is the original sign of -primeSymmetric. "
                        + "The Archimedean term remains owned by ZetaGamma.ArchimedeanJumpDecomposition; "
                        + "its actual Gamma comparison is owned by ZetaGamma.PeriodicEnergyComparison. "
                        + "This prime identity supplies no Gamma or pole term, no finite Schur margin, "
                        + "and no positivity certificate for the full physical Weil form."))),
                    DescribeRole.Theorem))));
    }
}
