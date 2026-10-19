using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class PositiveBranchReachableResponseDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Measurement/PositiveBranchReachableResponse.";
    private static readonly Formula K = F.Id("K"), E = F.Id("E"), C = F.Id("c"), U = F.Id("U");
    private static readonly Formula A = F.Id("A"), N = F.Id("N"), L = F.Id("L"), V = F.Id("v");
    private static readonly Formula Q = SigmaLower, T = Theta, Tzero = Sub(Theta, D(0));
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Real = Seq(Mathbb, Grp(F.Id("R")));
    private static readonly Formula Complex = Seq(Mathbb, Grp(F.Id("C")));
    private static readonly Formula Dim = F.Id("d"), Index = F.Id("n"), Kind = F.Id("Type");
    private static readonly Formula World = F.Id("Theta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly positive branch weights preserve the original Kraus word support. Termination from one "
            + "initial positive matrix then controls every state on its reachable space, uniformly on compact parameter sets.",
        H("Positive Branch Reachability and Response"),
        Blocks(
            Paragraph(Text("For finite index sets n and A, let K_a be complex n by n matrices, let c_a be strictly "
                + "positive real weights, and let rho be positive semidefinite. Write T(X) = sum_a c_a K_a X K_a^*, "
                + "R_l = sum_{k=0}^l T^k(rho), and supp(X) = ker(X) perpendicular. The empty Kraus word is the identity. "
                + "W_l(K,rho) is the complex span of K_w v for words of length at most l and v in supp(rho); "
                + "S(K,rho) is the union, equivalently the supremum, of these increasing subspaces. "
                + "Quadratic forms use the Euclidean inner product and their real parts.")),
            Theorem("support", "finite_orbit_support_eq_word_span", "Finite orbits and original words", SupportFormula(),
                "A positive weighted sum has zero quadratic form exactly when every summand has zero quadratic form. "
                + "Applying this to rho + T(R_l) identifies its kernel with the vectors killed by rho after every "
                + "adjoint Kraus word of length at most l+1. Taking orthogonal complements gives the support equality "
                + "for each l. Strict positivity of every weight is essential; no normalization or completeness is needed."),
            Theorem("faithful", "finite_reachable_faithful_sum", "A finite faithful sum on the reachable space", FaithfulFormula(),
                "The increasing word spans stabilize in a finite dimensional space. Choose L after stabilization. "
                + "The support equality identifies supp(R_L) with S(K,rho). A positive semidefinite operator has a "
                + "strictly positive quadratic form on the unit sphere of its support; compactness gives a uniform "
                + "lower bound mu. When rho is zero, the reachable space is zero and any positive mu works."),
            Theorem("gap", "initial_termination_uniform_reachable_gap", "From one terminating state to a common block gap", GapFormula(),
                "Assume T^*(I) <= I, with adjoint taken in the trace pairing. The survival effects (T^*)^k(I) "
                + "decrease to a positive fixed effect F. Termination of the original rho gives Tr(rho F)=0, hence "
                + "F kills the range of the finite faithful orbit sum and therefore all of S(K,rho). Convergence "
                + "on its unit sphere gives a block N >= 1 with survival at most one half. The spectral decomposition "
                + "of any supported positive matrix transports the quadratic bound to its trace. No return effect "
                + "is assumed to preserve S, and termination is not assumed for arbitrary ambient states."),
            Paragraph(Text("For a topological parameter space Theta and U contained in Theta, now let c(theta,a) be "
                + "continuous and strictly positive on U. Keep K_a and the positive return matrices E_a fixed, "
                + "and assume T_theta^*(I) + sum_a c(theta,a) E_a = I throughout U. Fix theta_0 in U and the same "
                + "positive rho, terminating at theta_0. In the following formula P(theta,X) denotes sum_{k>=0} "
                + "T_theta^k(X), J_theta = I - T_theta^*(I), and V(K,rho) is the real span of all positive matrices "
                + "supported on S(K,rho). Summability always refers to the entire displayed sequence. "
                + "For each compact nonempty B contained in U, g(B) = min(1, inf_{theta in B} inf_{a in A} "
                + "c(theta,a)/c(theta_0,a)); an empty branch family uses g(B)=1.")),
            Theorem("absorption", "positive_branch_compact_absorption", "All internal parameters and compact geometric tails", AbsorptionFormula(),
                "One common block N comes from the gap at theta_0. On a compact set B, positivity and continuity "
                + "give 0 < g(B) <= 1. Comparison of the positive maps and return effects gives "
                + "I-(T_theta^*)^N(I) >= g(B)^N [I-(T_theta_0^*)^N(I)] on S. Iteration yields the geometric bound "
                + "with eta = g(B)^N/2. Singletons give termination and summability at every internal parameter. "
                + "Summing the orbit gives the Poisson equation; continuity of the trace pairing gives the actual "
                + "event response, its nonnegativity and its mass bound. Taking the full return effect recovers "
                + "the whole initial trace. Real linearity extends the Poisson identity to V(K,rho)."),
            Paragraph(Text("For a finite fixed source instrument, group the Kraus maps into the original source branches. "
                + "The weights 1, p, 1-p, q, 1-q are positive on the open source square, so the same reachable space "
                + "works throughout that square. The block length and compact constants depend on the fixed instrument; "
                + "they are not asserted to be uniform over different controllers or at source endpoints.")),
            Paragraph(Text("For response coordinates, let Z be the real span of the original CP branch words applied to rho. "
                + "This space contains rho, is invariant under every source branch and is independent of p and q. It lies in "
                + "the Hermitian matrices supported on S. Thus D = dim_R Z <= dim_C(S)^2 <= d^2. Fix one real basis of Z. "
                + "The preceding summable Poisson identity restricts to Z: the sum of the iterates is an inverse "
                + "of I-M_theta. Finite dimensional injectivity and surjectivity agree, so this inverse exists on all "
                + "of Z, including directions outside the positive cone.")),
            Paragraph(Text("For an event with initial mass gamma_E and return effect F_E,theta, the actual probability is "
                + "gamma_E + ell_E,theta (I-M_theta)^{-1} rho_V, where ell_E,theta(X)=Tr(F_E,theta X). "
                + "The source conditions gamma_E >= 0, gamma_E+Tr(rho) <= 1 and 0 <= F_E,theta <= J_theta put this "
                + "response in [0,1]. Along an affine physical source line, M_theta and ell_E,theta have real affine "
                + "entries. The determinant denominator has degree at most D and is nonzero on the open physical "
                + "segment. The adjugate has degree at most D-1, so the numerator, including the initial mass term, "
                + "also has degree at most D. The response is real analytic there. If D=0 the response is constant.")),
            Paragraph(Text("For the four-cell target with B equal to 2 or 4, 1 <= C <= 1024/225, beta > 0 and "
                + "0 < h <= 1/4, the legal c=1 subfamily already obstructs a finite dimensional fixed source "
                + "instrument. Only fresh classical source outcomes carry the unknown rates; the Kraus maps, terminal "
                + "effects and initial data are fixed. For the chosen request the target mass of (x,z) is "
                + "u_x/2 + (h^beta/16)(-1)^(x+z), with u_1 the requested source rate and u_0=1-u_1. "
                + "On c=1, p=q=t=(1-h/C)/B, so the (1,0) response must equal "
                + "f(t)=t/2-[C(1-Bt)]^beta/16 on ((1-1/(4C))/B,1/B). "
                + "The rational response must remain a probability on the full internal source interval. "
                + "Analytic continuation of the target marginal toward zero forces a negative response at positive internal rates, contradicting "
                + "nonnegativity. This argument includes positive integer beta.")),
            Paragraph(Text("For a fixed dimension cap d, a hypothetical sequence of controllers with uniform total "
                + "variation error tending to zero would give rational functions of degrees bounded by d^2. "
                + "Normalize each numerator-denominator coefficient pair to norm one and pass to a convergent "
                + "subsequence. The full interval probability bounds exclude a zero limiting denominator; on an "
                + "open interval avoiding its finitely many roots, the limit equals the target. The same analytic "
                + "and nonnegativity obstruction yields a contradiction. Hence the uniform error has a strictly "
                + "positive lower bound for each d. This conclusion gives no rate and does not require a compact "
                + "parameter space of quantum realizations or a quantum realization of the limiting rational function.")))));

    private static DocumentBlock.Describe Theorem(string id, string declaration, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create("positive-branch-" + id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula Generic(Formula body) => All(Index, Kind, All(A, Kind,
        Seq(Call("Finite", Index), Sp, Land, Sp, Call("Finite", A), Sp, Rightarrow, Sp,
            All(K, Arrow(A, Mat(Index)), All(C, Arrow(A, Real), All(Rho, Mat(Index),
                Seq(Call("Positive", C), Sp, Land, Sp, Psd(Rho), Sp, Rightarrow, Sp, body)))))));
    private static Formula SupportFormula() => Disp(Generic(All(L, Nat,
        Eqn(Supp(Call("R", K, C, Rho, L)), Call("W", K, Rho, L)))));
    private static Formula FaithfulFormula() => Disp(Generic(Ex(L, Nat, Ex(Mu, Real,
        Seq(D(0), Sp, Lt, Sp, Mu, Sp, Land, Sp,
            Eqn(Supp(Call("R", K, C, Rho, L)), Space(K, Rho)), Sp, Land, Sp,
            Forall, Sp, V, Sp, InMacro, Sp, Space(K, Rho), Comma, Sp,
            Mu, Sp, NormSq(V), Sp, Leq, Sp, QuadForm(Call("R", K, C, Rho, L), V))))));
    private static Formula GapFormula() => Disp(All(Dim, Nat, All(A, Kind,
        Seq(Call("Finite", A), Sp, Rightarrow, Sp,
            All(K, Arrow(A, Mat(Dim)), All(C, Arrow(A, Real), All(Rho, Mat(Dim),
                Seq(Call("Positive", C), Sp, Land, Sp, Psd(Rho), Sp, Land, Sp,
                    Call("Dual", K, C, D(1)), Sp, Leq, Sp, D(1), Sp, Land, Sp,
                    Call("Tr", Orbit(K, C, Rho, F.Id("k"))), Sp, To, Sp, D(0),
                    Sp, Open, F.Id("k"), Sp, To, Sp, Infty, Close, Sp, Rightarrow, Sp,
                    Ex(N, Nat, Seq(D(1), Sp, Leq, Sp, N, Sp, Land, Sp,
                        Open, Forall, Sp, V, Sp, InMacro, Sp, Space(K, Rho), Comma, Sp,
                        QuadForm(Call("Survival", K, C, N), V), Sp, Leq, Sp, Half(NormSq(V)), Close,
                        Sp, Land, Sp, All(Q, Mat(Dim), Seq(Psd(Q), Sp, Land, Sp,
                            Supp(Q), Sp, Subseteq, Sp, Space(K, Rho), Sp, Rightarrow, Sp,
                            ReTr(Orbit(K, C, Q, N)), Sp, Leq, Sp, Half(ReTr(Q))))))))))))));
    private static Formula AbsorptionFormula()
    {
        Formula ct = Call("c", T), p = Call("P", T, Q), j = Sub(F.Id("J"), T), f = F.Id("F"), k = F.Id("k"), x = F.Id("X");
        Formula supported = Seq(Psd(Q), Sp, Land, Sp, Supp(Q), Sp, Subseteq, Sp, Space(K, Rho));
        Formula response = All(f, Mat(Dim), Seq(D(0), Sp, Leq, Sp, f, Sp, Leq, Sp, j, Sp, Rightarrow, Sp,
            Call("Summable", Seq(k, Sp, Mapsto, Sp, Call("Tr", Seq(f, Sp, Orbit(K, ct, Q, k))))), Sp, Land, Sp,
            Eqn(Call("Sum", Seq(k, Sp, Mapsto, Sp, Call("Tr", Seq(f, Sp, Orbit(K, ct, Q, k))))), Call("Tr", Seq(f, Sp, p))),
            Sp, Land, Sp, D(0), Sp, Leq, Sp, ReTr(Seq(f, Sp, p)), Sp, Leq, Sp, ReTr(Q), Sp, Land, Sp,
            Open, Eqn(f, j), Sp, Rightarrow, Sp, Eqn(Call("Tr", Seq(f, Sp, p)), Call("Tr", Q)), Close));
        Formula pointwise = All(T, U, All(Q, Mat(Dim), Seq(supported, Sp, Rightarrow, Sp,
            ReTr(Orbit(K, ct, Q, k)), Sp, To, Sp, D(0), Sp, Open, k, Sp, To, Sp, Infty, Close, Sp, Land, Sp,
            Call("Summable", Seq(k, Sp, Mapsto, Sp, Orbit(K, ct, Q, k))), Sp, Land, Sp,
            Eqn(Seq(p, Minus, Call("T", K, ct, p)), Q), Sp, Land, Sp, response)));
        Formula linear = All(T, U, All(x, Call("V", K, Rho), Seq(
            Call("Summable", Seq(k, Sp, Mapsto, Sp, Orbit(K, ct, x, k))), Sp, Land, Sp,
            Eqn(Seq(Call("P", T, x), Minus, Call("T", K, ct, Call("P", T, x))), x))));
        Formula b = F.Id("B"), g = Call("g", b);
        Formula factor = Pow(Seq(D(1), Minus, Half(Pow(g, N))), Seq(Lfloor, Frac, Grp(k), Grp(N), Rfloor));
        Formula compact = All(b, Call("Set", World), Seq(Call("Compact", b), Sp, Land, Sp,
            b, Sp, Neq, Sp, Emptyset, Sp, Land, Sp, b, Sp, Subseteq, Sp, U, Sp, Rightarrow, Sp,
            D(0), Sp, Lt, Sp, g, Sp, Leq, Sp, D(1), Sp, Land, Sp,
            ScopedAll(T, b, All(Q, Mat(Dim), Seq(supported, Sp, Rightarrow, Sp, All(k, Nat,
                Seq(ReTr(Orbit(K, ct, Q, k)), Sp, Leq, Sp, factor, Sp, ReTr(Q)))))), Sp, Land, Sp,
            All(Q, Mat(Dim), Seq(supported, Sp, Land, Sp, Eqn(Call("Tr", Q), D(1)), Sp, Rightarrow, Sp,
                All(k, Nat, Seq(Call("Sup", b, Seq(T, Sp, Mapsto, Sp, ReTr(Orbit(K, ct, Q, k)))), Sp, Leq, Sp, factor))))));
        Formula conditions = Seq(
            ScopedAll(F.Id("a"), A, Psd(Call("E", F.Id("a")))), Sp, Land, Sp,
            ScopedAll(T, U, All(F.Id("a"), A, Seq(D(0), Sp, Lt, Sp, Call("c", T, F.Id("a"))))), Sp, Land, Sp,
            ScopedAll(F.Id("a"), A, Call("ContinuousOn", Seq(T, Sp, Mapsto, Sp, Call("c", T, F.Id("a"))), U)), Sp, Land, Sp,
            ScopedAll(T, U, Eqn(Seq(Call("Dual", K, ct, D(1)), Plus,
                Call("Sum", Seq(F.Id("a"), Sp, InMacro, Sp, A), Seq(Call("c", T, F.Id("a")), Sp, Call("E", F.Id("a"))))), D(1))),
            Sp, Land, Sp, Tzero, Sp, InMacro, Sp, U, Sp, Land, Sp, Psd(Rho), Sp, Land, Sp,
            Call("Tr", Orbit(K, Call("c", Tzero), Rho, k)), Sp, To, Sp, D(0), Sp, Open, k, Sp, To, Sp, Infty, Close);
        return Disp(All(Dim, Nat, All(A, Kind, All(World, Kind,
            Seq(Call("Finite", A), Sp, Land, Sp, Call("TopologicalSpace", World), Sp, Rightarrow, Sp,
                All(K, Arrow(A, Mat(Dim)), All(E, Arrow(A, Mat(Dim)),
                All(C, Arrow(World, Arrow(A, Real)), All(U, Call("Set", World), All(Tzero, World, All(Rho, Mat(Dim),
                    Seq(conditions, Sp, Rightarrow, Sp,
                        Ex(N, Nat, Seq(D(1), Sp, Leq, Sp, N, Sp, Land, Sp, Scope(pointwise), Sp, Land, Sp, Scope(linear), Sp, Land, Sp, compact))))))))))))));
    }

    private static Formula Sub(Formula x, Formula i) => Seq(x, Underscore, Grp(i));
    private static Formula Mat(Formula n) => Seq(Sub(F.Id("M"), n), Open, Complex, Close);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula All(Formula x, Formula domain, Formula body) => Seq(Forall, Sp, x, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Scope(Formula body) => Seq(Open, body, Close);
    private static Formula ScopedAll(Formula x, Formula domain, Formula body) => Scope(All(x, domain, body));
    private static Formula Ex(Formula x, Formula domain, Formula body) => Seq(Exists, Sp, x, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Call(string f, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(f)), Open, Seq(args.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x }).ToArray()), Close);
    private static Formula Psd(Formula x) => Seq(x, Sp, Geq, Sp, D(0));
    private static Formula Supp(Formula x) => Call("supp", x);
    private static Formula Space(Formula k, Formula rho) => Call("S", k, rho);
    private static Formula Pow(Formula x, Formula p) => Seq(Open, x, Close, Caret, Grp(p));
    private static Formula Half(Formula x) => Seq(Frac, Grp(x), Grp(D(2)));
    private static Formula NormSq(Formula x) => Seq(Vert, Sp, x, Vert, Caret, Grp(D(2)));
    private static Formula QuadForm(Formula m, Formula v) => Call("Re", Seq(Langle, Sp, v, Comma, Sp, m, Sp, v, Sp, Rangle));
    private static Formula Orbit(Formula k, Formula c, Formula x, Formula j) => Call("Iter", Call("T", k, c), j, x);
    private static Formula ReTr(Formula x) => Call("Re", Call("Tr", x));
}
