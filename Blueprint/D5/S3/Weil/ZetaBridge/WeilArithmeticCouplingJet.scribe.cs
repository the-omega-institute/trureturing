using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilArithmeticCouplingJetDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet.";
    private static Formula Call(string name, params Formula[] args)
    {
        var result = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { result.Add(Comma); result.Add(Sp); }
            result.Add(args[i]);
        }
        result.Add(Close);
        return Seq(result.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), n = F.Id("n"), m = F.Id("m");
        Formula N = F.Id("N"), S = F.Id("S"), v = F.Id("v");
        Formula symbol = Call("s", c, n), budget = Call("B", c);
        Formula col = Call("Column", c, S, v, m), jet = Call("Jet", c, S, v, m);
        Formula mabs = Call("abs", m);
        Formula bound = Seq(Call("div", Seq(D(2), Sp, budget, Sp, N),
            Seq(F.Id("pi"), Sp, mabs, Sp, Grp(mabs, Minus, N))), Sp, Call("NormMass", S, v));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The explicit pole, Gamma and finite-prime boundary symbol controls "
                + "every exterior divided-difference coupling mode.",
            H("Weil Arithmetic Coupling Jet"),
            Blocks(
                Paragraph(Text(
                    "c is a natural number at least two, L=log(c), omega_n=2*pi*n/L, "
                    + "beta_j=2*j+1/2, and w_j=vonMangoldt(j)/sqrt(j). "
                    + "The symbol is s(c,n)=-2*omega_n*(cosh(L/2)-1)/(omega_n^2+1/4) "
                    + "-sum_{j>=0} omega_n*(1-exp(-beta_j*L))/(beta_j^2+omega_n^2) "
                    + "-sum_{j<c} w_j*sin(omega_n*log(j)). "
                    + "These are the actual boundary terms of the canonical arithmetic form. "
                    + "Their identification with its Fourier matrix follows the explicit "
                    + "calculations in Connes, Consani and Moscovici, arXiv:2511.22755, "
                    + "Lemma 2.3 and Section 4, and is a paper bridge in the existing source analysis.")),
                Describe.Lean(
                    DescribeId.Create("arithmetic-boundary-symbol"),
                    DeclarationHandle.Create(Owner + "arithmeticBoundarySymbol"),
                    H("The full arithmetic boundary symbol"),
                    StatementSource.FromAuthor(Disp(Seq(symbol, Eq,
                        Call("PoleGammaPrimeSineExpression", c, n)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "PoleGammaPrimeSineExpression is the explicit expression in the "
                        + "introductory paragraph. The prime cutoff is the integer c, "
                        + "with its endpoint omitted since the endpoint sine is zero. "
                        + "No zeta zero positions or lowest eigenvectors enter."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("arithmetic-boundary-budget"),
                    DeclarationHandle.Create(Owner + "arithmeticBoundaryBudget"),
                    H("An independent arithmetic envelope"),
                    StatementSource.FromAuthor(Disp(Seq(budget, Eq,
                        D(2), Sp, Call("cosh", Call("HalfLog", c)), Plus,
                        Call("AbsolutePrimeWeightSum", c)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "HalfLog(c)=log(c)/2. AbsolutePrimeWeightSum(c) is the finite sum "
                        + "of |vonMangoldt(j)/sqrt(j)| over 0<=j<c. The two nonprime "
                        + "contributions are bounded by 2*(cosh(L/2)-1) and 2."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("arithmetic-boundary-symbol-bound"),
                    DeclarationHandle.Create(Owner + "arithmetic_boundary_symbol_bound"),
                    H("Convergence and an unconditional arithmetic symbol bound"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Rightarrow, Sp,
                        Call("AbsoluteGammaSineSummability", c, n), Land, Sp,
                        Call("abs", symbol), Leq, Sp, budget))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "n is any integer. The Gamma sine series is absolutely convergent "
                        + "and |s(c,n)|<=B(c). The proof majorizes its absolute terms by "
                        + "|omega|/((2*j+1/2)^2+omega^2), proves a telescoping bound on "
                        + "every partial sum, and then controls the pole and prime terms. "
                        + "It assumes no operator-norm bound, Gamma-tail sign, spectral gap "
                        + "or Riemann hypothesis."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("coupling-column"),
                    DeclarationHandle.Create(Owner + "couplingColumn"),
                    H("The arithmetic exterior coupling column"),
                    StatementSource.FromAuthor(Disp(Seq(col, Eq,
                        Call("DividedDifferenceSum", c, S, v, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For a finite set S of integers and v:Z->C, this is "
                        + "sum_{n in S} ((s(c,n)-s(c,m))/(pi*(m-n)))*v_n, with the "
                        + "real coefficient cast to C. Exterior modes in the theorem "
                        + "cannot equal an interior mode, so no denominator vanishes."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("coupling-first-jet"),
                    DeclarationHandle.Create(Owner + "couplingFirstJet"),
                    H("Retain the two boundary moments"),
                    StatementSource.FromAuthor(Disp(Seq(jet, Eq,
                        Call("BoundaryMomentJet", c, S, v, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The definition is sum_{n in S} ((s(c,n)-s(c,m))/(pi*m))*v_n. "
                        + "Collecting this finite sum gives (b0-s(c,m)*a0)/(pi*m), "
                        + "where a0=sum v_n and b0=sum s(c,n)*v_n. "
                        + "No boundary moment is required to vanish."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("arithmetic-coupling-first-jet-error"),
                    DeclarationHandle.Create(Owner + "arithmetic_coupling_first_jet_error"),
                    H("An all-scale exterior coupling remainder"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("AtLeastTwo", c), Land, Sp, Call("Nonnegative", N), Land, Sp,
                        Call("InteriorIndicesBounded", S, N), Land, Sp, Call("Exterior", m, N),
                        Rightarrow, Sp, Call("norm", Seq(col, Minus, jet)), Leq, Sp, bound))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "N is real and nonnegative, every n in S satisfies |n|<=N, "
                        + "and Exterior(m,N) means N<|m|. NormMass(S,v)=sum_{n in S}|v_n|. "
                        + "The coefficient difference is exactly "
                        + "(s(c,n)-s(c,m))*n/(pi*m*(m-n)). The arithmetic envelope "
                        + "and |m-n|>=|m|-N prove the displayed estimate. "
                        + "There is no upper exterior cutoff. The infinite Gram tail bound, "
                        + "the verified interval inequalities at c=3, and the resulting "
                        + "paper/computer-assisted full-space simple-even statement are "
                        + "documented separately; they are not asserted as Lean results "
                        + "of this declaration. No unbounded-scale ground-mode convergence "
                        + "to Xi is proved."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "SOURCE_ONLY_UNCOMPILED candidate: the smooth-weight descriptions below "
                    + "belong to WeilArithmeticCouplingJet and retain the actual native operands. "
                    + "They use the existing pole and convergent Gamma series, with "
                    + "w(c,m)=(P(c,m)+G(c,m))/m^2=H(c,m)/m^2 and A=-H-S. "
                    + "Fresh source bindings, Scribe emission and faithful Reg registration "
                    + "remain caller-owned obligations for the changed source hash.")),
                Describe.Lean(
                    DescribeId.Create("smooth-envelope"),
                    DeclarationHandle.Create(Owner + "smoothEnvelope"),
                    H("The two actual Gamma bounds in one minimum"),
                    StatementSource.FromAuthor(Disp(Seq(Call("E", c, m), Eq,
                        Call("min", Seq(D(2), Plus, Call("div", Call("U", c), m)),
                            Seq(Call("div", F.Id("pi"), D(4)), Plus,
                                Call("div", Seq(Call("U", c), Plus,
                                    Call("div", D(3), Seq(D(4), Sp, Call("a", c)))), m)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For natural c,m this is exactly min(2+U(c)/m,pi/4+(U(c)+3/(4*a(c)))/m). Here L=log(c), a=2*pi/L and U=2*(cosh(L/2)-1)/a. Lean division is total; the estimates below use positive modes and c>=2. This is a finite envelope at every positive mode. Its fixed-c limit pi/4 and the corresponding square coefficient pi^2/16 are asymptotic interpretations still requiring real scoped verification; they are not new Lean limit theorems."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("smooth-weight"),
                    DeclarationHandle.Create(Owner + "smoothWeight"),
                    H("The actual nonnegative smooth weight"),
                    StatementSource.FromAuthor(Disp(Seq(Call("w", c, m), Eq, Call("div", Seq(Call("P", c, m), Plus, Call("G", c, m)), Call("square", m))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("P is exactly poleSine(L,frequency(c,m)); G is exactly tsum_j gammaSineTerm(L,frequency(c,m),j) from the native owner. Thus H=P+G=m^2*w and A=-H-S, with H the positive smooth mass and no new Gamma object. This definition is not a claim that Gamma itself is monotone."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("smooth-weight-nonneg"),
                    DeclarationHandle.Create(Owner + "smooth_weight_nonneg"),
                    H("Nonnegativity after division by the mode square"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Positive", m), Rightarrow, Call("Nonnegative", Call("w", c, m))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For natural c>=2 and m>0, 0<=w(c,m). The factors 1-exp(-(2*j+1/2)*log(c)) and cosh(log(c)/2)-1 are nonnegative. The actual convergent Gamma sum is retained."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("smooth-weight-antitone"),
                    DeclarationHandle.Create(Owner + "smooth_weight_antitone"),
                    H("Antitonicity of the actual smooth weight"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Positive", n), Land, Sp, n, Leq, Sp, m, Rightarrow, Call("w", c, m), Leq, Call("w", c, n)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For natural c>=2 and 0<n<=m, w(c,m)<=w(c,n). Each normalized Gamma summand is a nonnegative constant divided by m*((2*j+1/2)^2+a^2*m^2). The pole has the same form with r^2=1/4. Compare positive denominators and use the two actually summable divided Gamma series; no differentiation or divergent interchange occurs."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("smooth-weight-envelope"),
                    DeclarationHandle.Create(Owner + "smooth_weight_envelope"),
                    H("The minimum envelope at every later positive mode"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Land, Call("Positive", n), Land, Sp, n, Leq, Sp, m, Rightarrow, Call("Nonnegative", Call("E", c, n)), Land, Call("square", m), Sp, Call("w", c, m), Leq, Call("E", c, n)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For natural c>=2 and 0<n<=m, 0<=E(c,n) and m^2*w(c,m)<=E(c,n). The old Gamma <=2 and the new Gamma <=pi/4+3/(4*a*m) bounds are both consumed, at positive frequency omega=a*m. The new private proof uses f(x)=omega/(omega^2+x^2) and g(t)=f(2*t+1/2). Pinned AntitoneOn.sum_le_integral compares each finite shifted lattice sum with its interval integral. Pinned intervalIntegral.mul_integral_comp_mul_add and integral_div_sq_add_sq give twice that integral as arctan((2*M+1/2)/omega)-arctan((1/2)/omega). Antitonicity of f gives arctan((1/2)/omega)>=f(1/2)/2, so the complete partial sum is <=pi/4+3*f(1/2)/4<=pi/4+3/(4*omega). The original summability and actual sine-factor majorization pass this to the genuine Gamma tsum for log(c)>=0. No monotonicity of Gamma mass is used, and no cutoff restriction is added. This complete source attempt remains SOURCE_ONLY_UNCOMPILED."))),
                    DescribeRole.Theorem),
                // SOURCE_ONLY_UNCOMPILED. Insert these Blocks arguments immediately before
                // the existing arithmetic-symbol-smooth-split Describe.Lean in Create().
                // Reuse the pinned canonical Owner, Call, c, m, F and DefinitionDsl bindings.
                Paragraph(Text(
                    "SOURCE_ONLY_UNCOMPILED finite-block addition. Here H(c,m)=m^2*smoothWeight(c,m) "
                    + "is the POSITIVE smooth mass and the actual symbol is A=-H-S, where S is "
                    + "the existing finite-prime sine sum. This fixes the sign convention for "
                    + "all smooth-weight descriptions using the same positive-H convention.")),
                Describe.Lean(
                    DescribeId.Create("smooth-floor"),
                    DeclarationHandle.Create(Owner + "smoothFloor"),
                    H("An explicit smooth-mass floor"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("smoothFloor", c), Eq,
                        Call("div", Seq(D(1), Minus,
                            Call("exp", Call("div", Seq(Minus, Call("logLength", c)), D(2)))), D(1, 0))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For natural c, smoothFloor(c)=(1-exp(-logLength(c)/2))/10, with "
                        + "logLength(c)=log(c). It is strictly positive under c>=2. This is an "
                        + "explicit finite-block lower constant; no sharp asymptotic value is asserted."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("smooth-weight-floor"),
                    DeclarationHandle.Create(Owner + "smooth_weight_floor"),
                    H("A positive floor for the actual pole plus Gamma mass"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("AtLeastTwo", c), Land, Sp, Call("Positive", m), Land, Sp,
                        D(1), Leq, Sp, Call("omega", c, m), Rightarrow, Sp,
                        Call("Positive", Call("smoothFloor", c)), Land, Sp,
                        Call("smoothFloor", c), Leq, Sp,
                        Call("square", m), Sp, Call("smoothWeight", c, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The exact telescope is {c m : Nat}, hc:2<=c, hm:0<m, "
                            + "hw:1<=frequency(c,(m:Int)). Here omega(c,m) denotes exactly that "
                            + "frequency. The conclusion retains both 0<smoothFloor(c) and "
                            + "smoothFloor(c)<=m^2*smoothWeight(c,m), for every such c and m. "
                            + "The weight is the original poleSine plus the actual convergent "
                            + "gammaSineTerm series, divided by m^2.")),
                        Paragraph(Text(
                            "Fix the actual L=logLength(c)>0 and w=omega(c,m)>=1. Put "
                            + "eta=1-exp(-L/2)>0 and N=Nat.ceil(w). For each j<N, Nat.lt_ceil "
                            + "gives j<w, so 1/2<=gammaRate(j)<=3*w and "
                            + "gammaRate(j)^2+w^2<=10*w^2. Exponential monotonicity gives "
                            + "1-exp(-gammaRate(j)*L)>=eta. Two positive division comparisons, "
                            + "one for the denominator and one for the numerator, give "
                            + "gammaSineTerm(L,w,j)>=eta/(10*w). Nat.le_ceil gives "
                            + "w<=N, so this finite block has sum at least eta/10. Only then "
                            + "Summable.sum_le_tsum, using gamma_positive_summable and "
                            + "gamma_positive_nonneg, passes to the genuine owner Gamma sum. "
                            + "The pole is nonnegative by cosh(L/2)>=1 and w>=1; cancellation "
                            + "of the positive mode square uses the shared owner smooth_mass_eq identity.")),
                        Paragraph(Text(
                            "The source-level new content is a lower bound obtained by a block "
                            + "whose length depends on the actual frequency; it is not a binding "
                            + "wrapper around an existing floor theorem. At c=2 this supplies "
                            + "the positive smooth mass needed by the beta-only lower-tail route, "
                            + "where the separate finite-prime sine sum vanishes. No separate "
                            + "c=2 or eventual specialization is added. For larger c, possible "
                            + "cancellation with S is not controlled by this theorem. No pi/4 "
                            + "asymptotics, full-symbol pointwise lower bound, operator positivity, "
                            + "Robin statement, RH statement or five-mode identification is claimed. "
                            + "Lean elaboration, kernel checking, registration binding, Scribe "
                            + "emission and official required checks remain unperformed."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("smooth-weight-actual-asymptotic"),
                    DeclarationHandle.Create(Owner + "smooth_weight_actual_asymptotic"),
                    H("The actual smooth mass has a pi/4 asymptotic with an explicit rate"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, c, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                        D(2), Le, Sp, c, Rightarrow, Sp,
                        Exists, Sp, F.Id("K"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                        D(0), Lt, F.Id("K"), Land, Sp,
                        Forall, Sp, m, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                        D(0), Lt, m, Rightarrow, Sp,
                        Lvert, Sp, m, Caret, Grp(D(2)), Cdot, Call("smoothWeight", c, m),
                        Minus, Frac, Grp(Pi), Grp(D(4)), Rvert, Le,
                        Frac, Grp(F.Id("K")), Grp(m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every natural c with hc:2<=c there exists one real K>0, "
                            + "depending only on c, such that for every natural m>0, "
                            + "abs(m^2*smoothWeight(c,m)-pi/4)<=K/m. The selected declaration "
                            + "retains the actual poleSine and the genuinely convergent "
                            + "gammaSineTerm series in their original owner. It has no "
                            + "frequency threshold and includes m=1.")),
                        Paragraph(Text(
                            "Write L=log(c)>0, a=2*pi/L>0, w=a*m, "
                            + "C=exp(-L/2)/(1-exp(-2*L)), and U=2*(cosh(L/2)-1)/a. "
                            + "The existential proof takes K=explicitSmoothK(c)=U+(1+C)/a "
                            + "and reuses explicitSmoothK_spec before introducing m. "
                            + "The half-shifted Cauchy majorant has sum at least "
                            + "pi/4-1/(4*w), by left-endpoint integral comparison, the "
                            + "exact finite arctan substitution and its pi/2 endpoint limit. "
                            + "Mathlib's arctan_le_self bounds the initial shift error. "
                            + "The removed nonnegative exponential correction is truly "
                            + "summable and at most exp(-L/2)/(w*(1-exp(-2*L))), by a "
                            + "positive geometric majorant. Subtraction uses both summability "
                            + "hypotheses. Combining that lower bound with the existing "
                            + "smooth_mass_bounds upper estimate proves the absolute bound.")),
                        Paragraph(Text(
                            "For each fixed c at least 2, the constant K is chosen before m. "
                            + "The estimate holds for every positive natural m, including m=1. "
                            + "It gives no constant uniform in c and by itself establishes "
                            + "neither a coefficient-uniform tail bound nor RH."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("explicit-smooth-k"),
                    DeclarationHandle.Create(Owner + "explicitSmoothK"),
                    H("An explicit constant for the complete smooth mass"),
                    StatementSource.FromAuthor(Disp(Seq(Call("K", c), Eq,
                        Call("div", Seq(D(2), Sp, Call("coshMinusOne", Call("HalfLog", c)),
                            Plus, D(1), Plus, Call("GammaCorrection", c)), Call("a", c))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For L=log(c), a=2*pi/L and C=exp(-L/2)/(1-exp(-2*L)), "
                        + "K(c)=(2*(cosh(L/2)-1)+1+C)/a. GammaCorrection denotes exactly C, "
                        + "and cosh-minus-one(x) denotes cosh(x)-1. This formula fixes K "
                        + "from c alone, with the entire exponential correction and pole term."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("explicit-smooth-k-spec"),
                    DeclarationHandle.Create(Owner + "explicitSmoothK_spec"),
                    H("The specified constant controls every positive mode"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastTwo", c), Rightarrow,
                        Call("Positive", Call("K", c)), Land, Forall, Sp, m,
                        InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                        Call("Positive", m), Rightarrow,
                        Lvert, Sp, m, Caret, Grp(D(2)), Cdot, Call("smoothWeight", c, m),
                        Minus, Frac, Grp(Pi), Grp(D(4)), Rvert, Leq,
                        Frac, Grp(Call("K", c)), Grp(m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every natural c>=2, K(c)>0 and the absolute error is at most "
                        + "K(c)/m for every positive natural m. The complete pole plus the "
                        + "convergent Gamma series remain in smoothWeight. The upper mass "
                        + "bound and the lower Gamma estimate use the same explicit constant. "
                        + "This specification also proves smooth_weight_actual_asymptotic. "
                        + "There is no lower frequency threshold; c=2 and m=1 are included."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("explicit-smooth-k-le"),
                    DeclarationHandle.Create(Owner + "explicitSmoothK_le"),
                    H("A cutoff bound for the same explicit constant"),
                    StatementSource.FromAuthor(Disp(Seq(Call("AtLeastThree", c), Rightarrow,
                        Call("K", c), Leq, Call("sqrt", c), Sp, Call("logLength", c)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every natural c>=3, K(c)<=sqrt(c)*log(c). Put s=sqrt(c). "
                        + "Then exp(-L/2)=1/s, exp(-2*L)=1/c^2 and "
                        + "2*(cosh(L/2)-1)+1=s+1/s-1<=s. The correction "
                        + "(1/s)/(1-1/c^2) is at most s, so the numerator is at most 2*s. "
                        + "Division by 2*pi/L and pi>=1 give the stated bound. This uses "
                        + "the same K as the all-positive-mode estimate above."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("arithmetic-symbol-smooth-split"),
                    DeclarationHandle.Create(Owner + "arithmetic_symbol_smooth_split"),
                    H("The exact native smooth and prime split"),
                    StatementSource.FromAuthor(Disp(Seq(Call("Positive", m), Rightarrow, Call("A", c, m), Eq, Minus, Call("square", m), Sp, Call("w", c, m), Minus, Call("OwnerPrimeRangeSum", c, m)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For every natural c and positive natural m, A(c,m)=-m^2*w(c,m)-sum_{q<c} primeWeight(q)*sin(frequency(c,m)*log(q)). No c>=2 assumption is needed for this identity. The downstream module uses the existing owner_prime_sum_eq to identify the finite range sum with T2.primeSymbol."))),
                    DescribeRole.Theorem))));
    }
}
