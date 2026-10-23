using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilInfiniteComplementLeakageDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage.";
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
    private static Formula Sq(Formula x) => Seq(Grp(x), Caret, Grp(D(2)));

    public DocumentDefinition Create()
    {
        Formula L = F.Id("L"), N = F.Id("N"), s = F.Id("s");
        Formula u = F.Id("u"), v = F.Id("v"), pi = F.Id("pi");
        Formula density = Call("D", L, N, u, v, s);
        Formula mass = Seq(Call("SquareMass", u), Plus, Call("SquareMass", v));
        Formula right = Seq(Call("div", D(4), Seq(D(3), Sp, Sq(pi))), Sp, mass);
        Formula statement = Seq(
            Call("Positive", N), Land, Sp, Call("Positive", L), Land, Sp,
            Call("SquareSummable", u), Land, Sp, Call("SquareSummable", v),
            Rightarrow, Sp,
            Call("IntervalIntegrableOnQuarterBand", L, N, u, v), Land, Sp,
            Call("NormalizedQuarterBandIntegral", L, N, u, v), Leq, Sp, right);
        return DocumentDefinition.Create(ScribeNode.Create(
            "A convergent infinite exterior Fourier tail has quantitatively little "
                + "mass in the low-frequency quarter band, without an upper mode cutoff.",
            H("Weil Infinite Complement Leakage"),
            Blocks(
                Paragraph(Text(
                    "L is a positive real window length and N is a positive natural number. "
                    + "The sequences u,v : N -> C are square summable, with no finite upper "
                    + "support constraint. SquareMass(u) is sum_j |u_j|^2. "
                    + "The private Cauchy sum C(d,u)=sum_j u_j/(d+j+1) is absolutely "
                    + "convergent for d>0. The phase-adjusted orthonormal Fourier basis "
                    + "on [-L/2,L/2] is (-1)^n/sqrt(L)*exp(2*pi*i*n*x/L). "
                    + "u_j and v_j index modes N+j+1 and -(N+j+1).")),
                Describe.Lean(
                    DescribeId.Create("exterior-fourier-density"),
                    DeclarationHandle.Create(Owner + "exteriorFourierDensity"),
                    H("An explicit infinite-tail Cauchy density"),
                    StatementSource.FromAuthor(Disp(Seq(density, Eq,
                        Call("div", L, Sq(pi)), Sp,
                        Sq(Call("sin", Seq(pi, Sp, s))), Sp,
                        Sq(Call("norm", Seq(
                            Call("C", Seq(N, Plus, s), u), Minus,
                            Call("C", Seq(N, Minus, s), v))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The formula is evaluated on |s|<=N/4, away from every denominator "
                        + "zero. Physical frequency is t=2*pi*s/L. The identification with "
                        + "the Fourier transform of a general L2 exterior mode expansion "
                        + "is proved on paper in the existing source analysis; it has not "
                        + "been imported as an extra Lean theorem or axiom."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("infinite-complement-low-frequency-mass"),
                    DeclarationHandle.Create(Owner + "infinite_complement_low_frequency_mass"),
                    H("Infinite tails cannot concentrate in the low-frequency quarter band"),
                    StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Positive(x) means 0<x. SquareSummable means Summable of the "
                        + "squared complex norms. IntervalIntegrableOnQuarterBand means "
                        + "Lebesgue interval integrability of D between -N/4 and N/4. "
                        + "NormalizedQuarterBandIntegral is (1/L)*integral_{-N/4}^{N/4}D(s) ds. "
                        + "The proof first bounds the inverse-square partial sums by a "
                        + "telescoping reciprocal difference. It then proves absolute "
                        + "convergence, Cauchy-Schwarz for the infinite response, uniform "
                        + "series continuity, and the integral inequality. Thus neither a "
                        + "nonconvergent total sum nor a nonintegrable total integral is "
                        + "being assigned zero to make the conclusion vacuous. "
                        + "The all-form-domain arithmetic lower bound beta(a,N), the "
                        + "explicit prime-containing scale example, and the full "
                        + "operator Schur estimate remain paper results in this increment. "
                        + "This theorem makes no assumption about a spectral gap, "
                        + "ground-state parity, or zeros of Xi."))),
                    DescribeRole.Theorem),
                new DocumentBlock.Section(H("Application to the full complex physical Fourier complement"), Blocks(
                    Paragraph(Text("Let L>0, let N>=1 be an integer, and let f:R->C be any representative with MemLp f 2 for Lebesgue measure restricted to W=Ioc(-L/2,L/2). Set f0=1_W*f, with its literal zero value off W. There is no global measurability condition on f away from W, nor any reality, parity, continuity, endpoint agreement, pole orthogonality, finite support or upper mode cutoff. Define e_n(x)=(-1)^n/sqrt(L)*exp(2*pi*i*n*x/L), for every integer n, and c_n=integral_W conj(e_n(x))*f(x) dx. Assume c_n=0 for every integer with |n|<=N. Conjugation is on the basis alone. All integrability and summability below follow from this MemLp2 hypothesis; they are not extra premises.")))),
                new DocumentBlock.Section(H("Existing sources and exact normalization"), Blocks(
                    Paragraph(Text("The existing D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension is the Ioc indicator. With a=-L/2, its window endpoint a+L is L/2. The same owner's FormCore.PeriodicSpectralEnergy.physicalCoeff is defined by sqrt(L)*fourierCoeff; its formula is expanded here, without attributing frozen status to an unfrozen extension of an older owner. Put U=AddCircle.liftIoc L (-L/2) f. The physical coefficient c_n is (-1)^n*sqrt(L)*fourierCoeff(U,n). The pinned Mathlib fourierCoeff_liftIoc_eq and fourierCoeffOn_eq_integral identify it with the literal conjugate-mode integral: Haar contributes 1/L, and sqrt(L)/L=1/sqrt(L). The integer phase is real, has norm one and square one. Thus e_n is the phase-adjusted orthonormal basis for physical Lebesgue energy, including negative n.")))),
                new DocumentBlock.Section(H("Genuine time integrability and representative independence"), Blocks(
                    Paragraph(Text("Finite window measure and MemLp.integrable (1<=2) give L1 on W. Multiplication by each continuous bounded conjugate mode proves genuine coefficient-product integrability. The continuous PLUS kernel K_t(x)=exp(I*t*x) has norm one for every real t and x, so f*K_t is integrable on W. IntegrableOn.integrable_indicator gives global L1 of f0, and bounded-kernel multiplication gives global integrability of f0*K_t for every real t. MemLp.integrable_norm_pow gives integrability of norm(f)^2 on W. These facts justify subtraction of actual coefficient pairings, window transforms and global residual transforms; no totalized undefined integral is used to establish the inequalities. Pulling back the actual toLp representative through AddCircle.measurePreserving_mk preserves a.e. equality. Integrating the difference of its coefficient products and the original f products gives zero, using both integrability proofs. Consequently all coefficients and transforms used below are those of the literal original f on W.")))),
                new DocumentBlock.Section(H("Complete Parseval mass and integer reindexing"), Blocks(
                    Paragraph(Text("The lift belongs to MemLp2 for probability Haar; let F be its MemLp.toLp representative. Mathlib hasSum_sq_fourierCoeff supplies the entire integer norm-square series. AddCircle.integral_preimage and volume_eq_smul_haarAddCircle transport physical Lebesgue energy as E=integral_W norm(f)^2=L*integral_circle norm(F)^2 dHaar. The actual a.e. representative equality identifies the integrals and coefficients. Since norm(c_n)^2=L*norm(fourierCoeff(F,n))^2, HasSum over all integers has sum E. Put u_j=c_(N+j+1), v_j=c_(-(N+j+1)), j>=0. Injective restriction proves summability of both norm-square sequences. Both finite prefixes of the positive and negative integer branches vanish by the low-coefficient hypothesis. The pinned hasSum_nat_add_iff and HasSum.of_add_one_of_neg_add_one reindex the complete series; uniqueness then gives sum_j norm(u_j)^2+sum_j norm(v_j)^2=E. This is a proved energy equality for the actual infinite exterior, not an assumed Parseval identity or a finite truncation.")))),
                new DocumentBlock.Section(H("The actual PLUS transform as a continuous linear functional"), Blocks(
                    Paragraph(Text("Zeta23.paperFT is the existing PLUS transform: T(t)=integral_R f0(x)*exp(I*t*x) dx. The indicator identity reduces it to integral_W f(x)*K_t(x) dx. Lift the conjugate kernel conj(K_t) to the circle and take its toLp class D_t. The continuous linear functional A_t(F)=L*inner(D_t,F), formed with Mathlib innerSL, equals this actual window transform by L2.inner_def, the a.e. kernel representative equality and the Ioc measure-preserving map. Its norm is at most L*integral_circle norm(F) dHaar, and integral_mul_norm_le_Lp_mul_Lq with Real.HolderConjugate.two_two bounds this L1 integral by norm(F). The nonnegative Bochner/lintegral identity, AddCircle.lintegral_preimage, volume=L*Haar and the actual toLp equality give sqrt(E)=sqrt(L)*norm(F). Applied to any literal MemLp2 residual r, these identities prove |paperFT(r0)(t)|<=sqrt(L)*sqrt(integral_W norm(r)^2), uniformly for every real t. The same derivation uses genuine energy integrability, not a separately assumed norm identity.")))),
                new DocumentBlock.Section(H("Full Fourier net and its physical uniform limit"), Blocks(
                    Paragraph(Text("Mathlib hasSum_fourier_series_L2 gives P_S=sum_(n in S) fourierCoeff(F,n) smul fourierLp(2,n) tending to F over atTop of all finite subsets S of Z. For each S the literal window residual is r_S(x)=P_S(x mod L)-F(x mod L). It belongs to MemLp2 by measure-preserving pullback and subtraction, and its lifted toLp representative is P_S-F by Lp.coeFn_sub and AddCircle.coe_equivIoc. Integrability of the global kernel products justifies integral_sub, so its actual PLUS transform is sum_(n in S) A_t(fourierCoeff(F,n) smul fourierLp(2,n))-A_t(F). The preceding physical residual estimate bounds its norm by sqrt(L)*sqrt(energy(r_S))=L*norm(P_S-F). Given epsilon>0, the full L2 net eventually has norm(P_S-F)<epsilon/L; that one finite-set threshold works for every real t. This proves convergence of the actual transformed net uniformly on R without restricting S to a terminal cutoff. At a fixed frequency the existing ContinuousLinearMap.hasSum applied to A_t and hasSum_fourier_series_L2 already supplies the HasSum statement directly. The full uniform derivation is an application of these existing ingredients and is not presented as a new exported theorem.")))),
                new DocumentBlock.Section(H("Mode integral, exact coefficient term and both signs"), Blocks(
                    Paragraph(Text("For any integer n and real s with n+s!=0, combine fourier_coe_apply with K_(2*pi*s/L) to get exp(2*pi*i*(n+s)*x/L). The oriented linear change of variable and Mathlib integral_exp_mul_I_eq_sin give the raw mode integral L*sin(pi*s)/pi * (-1)^n/(n+s), using Real.sin_add_int_mul_pi. Multiplying by the basis factor (-1)^n/sqrt(L) cancels the phase square and uses sqrt(L)^2=L, giving integral_W e_n(x)*K_(2*pi*s/L)(x) dx=sqrt(L)*sin(pi*s)/(pi*(n+s)). For the actual toLp representative, equality of integrable coefficient pairings proves fourierCoeff(F,n)*fourier_n(x)=c_n*e_n(x). Pull back coeFn_fourierLp through the same measure-preserving map, move the constant coefficient through the integral, and apply the preceding actual mode formula. Thus each transformed Fourier term is sqrt(L)*sin(pi*s)/pi * c_n/(n+s), with the normalization performed in the mode formula itself.")))),
                new DocumentBlock.Section(H("Absolute infinite Cauchy response and HasSum uniqueness"), Blocks(
                    Paragraph(Text("On |s|<=N/4 with N>=1, both N+s and N-s are positive. Every positive exterior denominator is N+s+j+1; every negative exterior denominator is -(N-s+j+1). The existing frozen inverse_square_summable and private Cauchy norm-summability proof in this leakage owner, combined with the proved square-summable tails, give absolute convergence of C(N+s,u)=sum_j u_j/(N+s+j+1) and C(N-s,v)=sum_j v_j/(N-s+j+1). The transformed positive branch has sum A*C(N+s,u) and the negative branch has sum -A*C(N-s,v), where A=sqrt(L)*sin(pi*s)/pi. Kill every central Fourier term by its zero coefficient before applying any non-pole formula; this also handles central poles without a false division premise. Integer reindexing gives HasSum of the full transformed series with value A*(C(N+s,u)-C(N-s,v)). Its actual transform value is supplied by the full uniform net, or directly by the existing continuous-linear-map HasSum theorem at this frequency. HasSum uniqueness proves T(2*pi*s/L)=A*(C(N+s,u)-C(N-s,v)). No conjugation of c_n, frequency reflection, missing negative sign or identification hypothesis occurs.")))),
                new DocumentBlock.Section(H("Squared density, closed physical band and Jacobian"), Blocks(
                    Paragraph(Text("Take complex norms and square the last identity. The actual squared PLUS transform equals the existing exteriorFourierDensity L N u v s, namely L/pi^2*sin(pi*s)^2*norm(C(N+s,u)-C(N-s,v))^2, on the entire closed quarter band. Apply the frozen infinite_complement_low_frequency_mass to the two proved square-summable tails. It supplies interval integrability and (1/L)*integral_(-N/4)^(N/4) density(s) ds <=4/(3*pi^2)*E after the proved Parseval mass equality. With k=2*pi/L>0, the endpoints k*(+/-N/4) are +/-pi*N/(2*L). IntervalIntegrable.comp_mul_left transports integrability through the inverse scaling, and intervalIntegral.smul_integral_comp_mul_left gives dt/(2*pi)=ds/L. Hence T has integrable squared norm on this physical band, and (1/(2*pi))*integral_(|t|<=pi*N/(2*L)) norm(T(t))^2 dt <=4/(3*pi^2)*integral_W norm(f)^2. The closed-band set is Icc(-R,R); integral_Icc_eq_integral_Ioc gives its Lebesgue endpoint a.e. bridge before intervalIntegral.integral_of_le identifies the oriented integral. Neither the full 1/(2*pi) normalization nor the exact 4/(3*pi^2) coefficient is absorbed into a definition.")))),
                new DocumentBlock.Section(H("The literal original L=2a application"), Blocks(
                    Paragraph(Text("For every a>0 put L=2*a. Algebra identifies Ioc(-L/2,-L/2+L) with Ioc(-a,a), the zero extension with the literal Ioc(-a,a).indicator f, and pi*N/(2*L) with pi*N/(4*a). The coefficient hypothesis is exactly integral_(Ioc(-a,a)) conj(e_n(x))*f(x) dx=0 for every integer |n|<=N. The preceding literal coefficient integral identity supplies the Fourier hypotheses. Therefore for every arbitrary complex MemLp2 function on Ioc(-a,a) and N>=1, (1/(2*pi))*integral_(|t|<=pi*N/(4*a)) norm(Zeta23.paperFT((Ioc(-a,a)).indicator f)(t))^2 dt <=4/(3*pi^2)*integral_(Ioc(-a,a)) norm(f)^2. The closed-band Icc/Ioc a.e. equality precedes use of the oriented interval inequality. Smooth periodic complex data are included, with no extra endpoint matching, parity, reality, pole orthogonality, finite support or cutoff hypothesis.")))),
                new DocumentBlock.Section(H("Attribution and scope"), Blocks(
                    Paragraph(Text("The coefficient estimate and its infinite Cauchy convergence proofs belong to this existing leakage owner. The physical derivation is the supplied r4476 scientific argument reviewed in r4490 and repaired in the sealed r4518 source; the independent r4523 review identifies it as reuse of the existing frontier. Fourier completeness, Parseval, Holder, elementary mode integration, a.e. transport, HasSum continuity and interval scaling use Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679. This application narrative exports no additional Lean declaration or theorem Describe and claims no independent literature novelty. It supplies no full arithmetic-form lower bound, Robin inequality, Schur or Riesz sign, completed-carrier realization, RH sign, whole-branch acceptance, freeze or required-CI result.")))))));
    }
}
