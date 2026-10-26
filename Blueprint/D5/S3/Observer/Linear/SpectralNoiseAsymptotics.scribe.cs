using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class SpectralNoiseAsymptoticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Noise scales for finite power-controlled spectra", H("Noise scales for finite power-controlled spectra"), Blocks(
            Describe.Lean(DescribeId.Create("spectral-noise-asymptotics"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/SpectralNoiseAsymptotics.spectral_noise_asymptotics"),
                H("Information growth and complete recovery"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let n be a nonnegative integer and let i range from zero through n. Choose nonnegative integer powers q(i), with q(i) at most q(n), and real functions lambda(i,T). Fix positive constants beta, c, and C. Assume that for every sufficiently small positive T and every i, c T raised to q(i) is at most lambda(i,T), and lambda(i,T) is at most C T raised to q(i). No continuity is required of these functions. In the display, powerBounds denotes these simultaneous eventual inequalities together with c and C positive and q(i) at most q(n).")),
                    Paragraph(Text("For every real alpha define I(alpha,T) as one half the sum over i of log(1+lambda(i,T)/(beta T raised to alpha)). Define R(alpha,T) as one half the sum of T raised to alpha divided by beta T raised to alpha plus lambda(i,T). For any positive variance schedule epsilon on all positive times, define R(epsilon,T) by replacing T raised to alpha in this latter expression with epsilon(T). All logarithms are natural.")),
                    Paragraph(Text("For every real alpha, including values equal to one or more occupied powers, the difference between I(alpha,T) and one half the sum of max(alpha-q(i),0) times log(1/T) is bounded as T decreases to zero. R(epsilon,T) tends to zero exactly when epsilon(T) is little-o of T raised to q(n), for every positive schedule without a continuity or power-law assumption. If alpha differs from every q(i), R(alpha,T) tends to the number of indices with q(i) greater than alpha, divided by 2 beta. Repeated powers are counted with their full multiplicity.")),
                    Paragraph(Text("Multiplying each logarithm's argument by T raised to max(alpha-q(i),0) puts it in the fixed positive interval from min(1,c/beta) to 1+C/beta. This gives a uniform bound for each logarithmic remainder. With delta(T)=epsilon(T)/T raised to q(n), all risk summands lie between zero and delta(T)/c, while the final summand is at least delta(T)/(beta delta(T)+C). Set v(T)=delta(T)/(beta delta(T)+C). The inverse relation delta=C v/(1-beta v) proves necessity of the recovery condition. The strict-threshold limit follows by separating powers above and below alpha."))), DescribeRole.Theorem),
            new DocumentBlock.Section(H("Noise selection of observable derivative layers"), Blocks(
            Paragraph(Text("Fix d,p>=1, real matrices B of size d by d and C of size p by d, and beta>0. Assume finite observability: C B^k x=0 for every 0<=k<d implies x=0. Put V_0=R^d, V_j=the intersection of ker(C B^k) for 0<=k<j, m=the least j with V_(j+1)=0, E_j=V_j intersect the orthogonal complement of V_(j+1), and d_j=dim E_j. Then m<d, d_m>0 and R^d is the orthogonal sum of E_0 through E_m. Fix B,C, the Euclidean norms and the time unit throughout the limit T down to zero through positive values.")),
            Paragraph(Text("For every T>0, the trajectory map F_T sends x to the L2 class of t mapped to C exp(t B)x on (0,T]. The construction and injectivity in "), Ref("D5/S3/Observer/Linear/ObservableTrajectoryCoordinates.observable_trajectory_coordinates"), Text(" give a d-dimensional image and hence an orthonormal image basis. Any bounded linear trajectory representative with this almost-everywhere formula equals F_T by equality of L2 classes. For any orthonormal basis b_(T,i) of that image, form the coordinate map U_T by projecting onto the image and applying its basis isometry. Its coordinates are the integrals of inner(b_(T,i)(t),g(t)) from zero to T. M_T is the matrix of U_T F_T. Since U_T is isometric on the image, M_T transpose M_T=F_T adjoint F_T=G(T), where G(T) is the integral of exp(t B transpose) C transpose C exp(t B) from zero to T. Thus all representatives and all orthonormal image bases give the same Gramian; neither a Gramian factor nor a spectral bound is an extra assumption.")),
            Paragraph(Text("On any probability space let X and xi be independent measurable random vectors with laws N(0,beta inverse I_d) and N(0,I_d). For any real amplitude sigma(T) with v(T)=sigma(T)^2>0 set Y_T=M_T X+sigma(T) xi. These are d finite normalized integral readings with independent isotropic coordinate noise. The law mu_T of (Y_T,X) is the actual pushforward of the same independent Gaussian pair, and I_T is the ENNReal KL divergence of mu_T from the product of its two marginals. Define R_T as the ENNReal infimum, over every measurable map a:R^d to R^d, of the nonnegative integral of ||X-a(Y_T)||^2/2. Infinite-risk competitors remain in this infimum. There is no white-noise random function in L2 in this experiment.")),
            Paragraph(Text("The posterior disintegration in "), Ref("D5/S3/Observer/Linear/GaussianObservationLaw.gaussian_observation_law"), Text(" applies with M=M_T and tau=v(T) inverse. Its covariance is Sigma_T=(beta I+v(T) inverse G(T)) inverse and its mean is v(T) inverse Sigma_T M_T transpose Y_T. The KL value is finite and equals one half log det(I+G(T)/(beta v(T))). Under each posterior, the conditional squared-loss integral for a is trace(Sigma_T)/2+||posterior mean-a(Y_T)||^2/2. Tonelli for the joint disintegration proves this identity for every measurable a, even when its risk is infinite. The linear posterior mean attains the infimum, so R_T=ofReal(trace(Sigma_T)/2) and R_T is finite. Real conversions of I_T and R_T below therefore preserve their values.")),
            Paragraph(Text("For the same posterior and prior, the expected conditional free-energy difference is beta inverse times I_T, with F(p)=expected ||x||^2/2 minus beta inverse times differential entropy. If B transpose=-B, exp(tB) is an isometry with inverse exp(-tB); composition with this inverse bijects all measurable future estimators. The future Bayes energy risk at every t>=0 is the same R_T. These are the information and risk quantities of the same Gaussian experiment.")),
            Paragraph(Text("The normalized physical scaling in "), Ref("D5/S3/Observer/Linear/DerivativeLayerNativeGramian.derivative_layer_native_gramian"), Text(" acts on E_j by sqrt(T) T^j and has a positive polynomial Gramian limit. An orthonormal basis subordinate to the E_j, reordered by increasing layer label w_i, satisfies #{i:w_i=j}=d_j and max_i w_i=m. Orthogonal conjugacy preserves the ordered spectrum of the actual G(T). Applying "), Ref("D5/S3/Observer/Linear/GradedCongruenceSpectrum.graded_congruence_spectrum"), Text(" in these coordinates gives constants c,K,delta>0 with c T^(2w_i+1)<=lambda_i(T)<=K T^(2w_i+1) for every i and 0<T<delta. All these objects come from the fixed observable B,C and the derivative filtration.")),
            Paragraph(Text("Diagonalizing this same G(T) expresses information as one half the sum of log(1+lambda_i(T)/(beta v(T))), and risk as one half the sum of v(T)/(beta v(T)+lambda_i(T)). Apply the finite-spectrum theorem above with n=d-1 and q(i)=2w_i+1. Grouping equal w_i counts exactly d_j terms. For every real alpha, with v(T)=T^alpha at every positive T, the information remainder is O(1), including alpha equal to occupied thresholds. The risk limit requires alpha unequal to 2j+1 only when d_j>0. Empty layers impose no exclusion.")),
            Paragraph(Math(TrajectoryApplicationFormula())),
            Paragraph(Text("In the display I_alpha and R_alpha use variance T^alpha, R_v uses an arbitrary schedule v:R to R positive at every T>0, and I_eta uses the constant variance eta>0. Each sum runs over j=0,...,m. In the risk-limit sum retain exactly the indices with 2j+1>alpha. The information coefficient is exactly one half, the unrecovered energy per direction is exactly 1/(2 beta), and the fixed-noise coefficient is exactly trace(C transpose C)/(2 beta eta). No monotonicity, continuity or measurability in T is imposed on v or on the family of trajectory bases. Every positive v admits an amplitude sigma(T)=sqrt(v(T)); either sign of any amplitude with that square gives the same laws.")),
            Paragraph(Text("For necessity and sufficiency of complete recovery set delta(T)=v(T)/T^(2m+1). The risk is at most d delta(T)/(2c), while one occupied last-layer direction contributes at least delta(T)/(2(beta delta(T)+K)). Thus risk tends to zero exactly when delta(T) tends to zero, which is precisely v=o(T^(2m+1)). This uses only the simultaneous two-sided spectral bounds and positivity of v. At an occupied equality alpha=2j+1 the information remains bounded in that layer; no universal risk limit is asserted there.")),
            Paragraph(Text("For constant eta, "), Ref("D5/S3/Observer/Linear/PhysicalFixedNoiseInformation.physical_fixed_noise_information"), Text(" gives constants A>=0 and epsilon>0 with |I_eta(T)-T trace(C transpose C)/(2 beta eta)|<=A T^2 for every 0<T<=epsilon. Its operator integral is this same G(T); standard orthonormal coordinates preserve determinant and trace. The fixed-noise clause uses the exponential observation directly and needs no observability assumption. Its first-order term reads the initial gain alone; it does not certify recovery of higher derivative layers. No conclusion about other unresolved operator-window alternatives is implied.")))))));

    private static Formula TrajectoryApplicationFormula()
    {
        Formula time = F.Id("T"), j = F.Id("j"), m = F.Id("m"), alpha = Alpha;
        Formula eta = F.Id("eta"), v = F.Id("v");
        Formula layer = Seq(F.Id("d"), Underscore, Grp(j));
        Formula power = Seq(D(2), j, Plus, D(1));
        Formula sum(Formula body) => Seq(Sum, Underscore, Grp(j, Eq, D(0)), Caret, Grp(m), Sp, body);
        Formula variancePower = Seq(time, Caret, Grp(Seq(D(2), m, Plus, D(1))));
        Formula logInverse = Seq(Log, Open, Frac, Grp(D(1)), Grp(time), Close);
        Formula growth = Seq(Frac, Grp(D(1)), Grp(D(2)), sum(Seq(layer, Sp,
            Call("max", Seq(alpha, Minus, Seq(Open, power, Close)), D(0)))), Sp, logInverse);
        Formula riskSum = sum(Seq(layer, Sp, Call("indicator", Seq(power, Gt, alpha))));
        Formula gram = Seq(F.Id("C"), Caret, Grp(F.Id("T")), F.Id("C"));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Call("I", alpha, time), Eq, growth, Plus, Call("O", D(1)),
            RowBreak, Grp(), Lim, Underscore, Grp(time, To, D(0), Caret, Grp(Plus)),
            Call("R", alpha, time), Eq, Frac, Grp(riskSum), Grp(D(2), Beta),
            RowBreak, Grp(), Call("R", v, time), To, D(0), Sp, Iff, Sp,
            Call("v", time), Eq, Call("o", variancePower),
            RowBreak, Grp(), Call("I", eta, time), Eq,
            Frac, Grp(time), Grp(D(2), Beta, Sp, eta), Call("tr", gram),
            Plus, Call("O", Seq(time, Caret, Grp(D(2)))),
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TheoremFormula()
    {
        Formula alpha = Alpha, time = F.Id("T"), eps = Varepsilon;
        Formula q = F.Id("q"), i = F.Id("i"), n = F.Id("n");
        Formula qi = Call("q", i), qn = Call("q", n);
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula growth = Seq(Frac, Grp(D(1)), Grp(D(2)), Sum, Underscore, Grp(i, Eq, D(0)),
            Caret, Grp(n), Sp, Call("max", Seq(alpha, Minus, qi), D(0)), Sp, Log, Open, Frac, Grp(D(1)), Grp(time), Close);
        Formula remainder = Seq(Call("I", alpha, time), Minus, growth, Eq, Call("O", D(1)));
        Formula epsTime = Seq(eps, Open, time, Close);
        Formula recovery = Seq(Lim, Underscore, Grp(time, To, D(0), Caret, Grp(Plus)), Call("R", eps, time), Eq, D(0),
            Sp, Iff, Sp, epsTime, Eq, Call("o", Seq(time, Caret, Grp(qn))));
        Formula count = Call("card", Seq(OpenBrace, i, Colon, Sp, qi, Gt, alpha, CloseBrace));
        Formula indexSet = Call("Fin", Seq(n, Plus, D(1)));
        Formula threshold = Seq(Forall, Sp, i, InMacro, indexSet, Comma, Sp, alpha, Neq, qi);
        Formula risk = Seq(Forall, Sp, alpha, InMacro, real, Comma, Sp, Open, threshold, Close, Sp, Rightarrow, Sp,
            Lim, Underscore, Grp(time, To, D(0), Caret, Grp(Plus)), Call("R", alpha, time), Eq,
            Frac, Grp(count), Grp(D(2), Sp, Beta));
        Formula positiveSchedule = Seq(Forall, Sp, time, Gt, D(0), Comma, Sp, epsTime, Gt, D(0));
        return Disp(Seq(Call("powerBounds", q, LambdaLower, F.Id("c"), F.Id("C")), Sp, Land, Sp,
            Beta, Gt, D(0), Sp, Rightarrow, Sp, Open,
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, alpha, InMacro, real, Comma, Sp, remainder,
            RowBreak, Grp(), Forall, Sp, eps, Colon, real, To, real, Comma, Sp,
            Open, positiveSchedule, Close, Sp, Rightarrow, Sp, Open, recovery, Close,
            RowBreak, Grp(), risk, End, Grp(F.Id("gathered")), Close));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
