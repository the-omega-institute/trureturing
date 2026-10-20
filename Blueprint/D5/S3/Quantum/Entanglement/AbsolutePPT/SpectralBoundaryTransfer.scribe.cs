using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class SpectralBoundaryTransferDocument : IScribeDocumentDefinition
{
    private static Formula D(long n) => Num(n);
    private static Formula X(string n) => F.Id(n);
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula N => Seq(Mathbb, Grp(X("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(X(name), [.. xs]);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp,y);
    private static Formula Imp(Formula p, Formula q) => Seq(Par(p), Rightarrow, Sp,Par(q));
    private static Formula And(params Formula[] fs) => Seq(fs.SelectMany((f,i) => i == 0 ? new[] {Par(f)} : new[] {Land, Sp,Par(f)}).ToArray());
    private static Formula All(string n, Formula t, Formula f) => Seq(Forall, Sp,Par(Seq(X(n), Colon, t)), Comma, Par(f));
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp,y);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Sq(Formula x) => new Formula.Power(Par(x), D(2));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Sum(string n, Formula t, Formula f) => Seq(new Formula.Subscript(F.Sum, Seq(X(n), Colon, t)), Par(f));
    private static Formula Vector(Formula n) => Arrow(Fin(n), R);
    private static Formula Mass(Formula n, Formula l) => Sum("i", Fin(n), new Formula.Apply(l, [X("i")]));
    private static Formula Purity(Formula n, Formula l) => Sum("i", Fin(n), Sq(new Formula.Apply(l, [X("i")])));
    private static Formula Feasible(Formula n, Formula l) => And(Call("Antitone", l),
        All("i", Fin(Add(n,D(9))), Le(D(0), new Formula.Apply(l, [X("i")]))),
        Eqn(Mass(Add(n,D(9)),l),D(1)),
        Call("PosSemidef",Call("K1",Call("boundaryValues",n,l))),
        Call("PosSemidef",Call("K2",Call("boundaryValues",n,l))));
    private static DocumentBlock Desc(string name, string title, Formula f, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("appt-spectral-transfer-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer." + name),
            H(title), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create()
    {
        var n=X("n"); var a=X("a"); var l=X("l"); var q=X("q");
        return DocumentDefinition.Create(ScribeNode.Create(
            "Rank-three and rank-four necessary spectral bounds transfer across actual middle multiplicities.",
            H("Boundary-preserving spectral insertion and deletion"), Blocks(
            Desc("boundaryIndex", "Extremal positions",
                All("n",N,All("q",Fin(D(9)),Eqn(Call("boundaryIndex",n,q),
                    Call("if",Seq(q,F.Lt,D(3)),q,Add(n,q))))),
                "A vector of length n+9 has boundary positions q for q<3 and n+q for q>=3. These are its top three and bottom six entries, including ties. The parameter n counts middle coordinates. The displayed indices denote their natural values in Fin (n+9).", DescribeRole.Definition),
            Desc("boundaryValues", "Boundary observation",
                All("n",N,All("l",Vector(Add(n,D(9))),All("q",Fin(D(9)),
                    Eqn(Call("boundaryValues",n,l,q),new Formula.Apply(l,[Call("boundaryIndex",n,q)]))))),
                "The observation retains the three largest and six smallest coordinates. It does not observe the middle coordinates separately. K1 and K2 are the existing real symmetric three-by-three boundary pencils of QutritSpectralReduction.", DescribeRole.Definition),
            Desc("purityBound", "Dimension-dependent purity value",
                All("N",N,Eqn(Call("purityBound",X("N")),Frac(Add(X("N"),D(8)),Sq(Add(X("N"),D(2)))))),
                "Natural dimensions are cast to the reals before division. The value is f(N)=(N+8)/(N+2)^2. The inner-polytope formula and the attaining spectrum (3,1,...,1)/(N+2) are due to Ahiable–Kothakonda–Winter, arXiv:2608.03390v2. Only the unrestricted upper-bound inference is a candidate addition here.", DescribeRole.Definition),
            Desc("SpectralBound", "A bound for the rank-three relaxation",
                All("n",N,Seq(Call("SpectralBound",n),Iff, Sp,All("l",Vector(Add(n,D(9))),
                    Imp(Feasible(n,l),Le(Purity(Add(n,D(9)),l),Call("purityBound",Add(n,D(9)))))))),
                "SpectralBound n is the universal square-sum upper bound for all antitone nonnegative mass-one vectors of length n+9 whose two boundary pencils are positive semidefinite. This is a spectral relaxation; no sufficiency assertion for literal APPT is included.", DescribeRole.Definition),
            Desc("spectral_bound_transfer", "Transfer from two endpoint dimensions",
                All("n",N,All("a",N,Imp(Le(D(1),a),Imp(Call("SpectralBound",n),
                    Imp(Call("SpectralBound",Add(Add(n,D(1)),a)),Call("SpectralBound",Add(n,D(1)))))))),
                "Put N=n+10 and let t be the actual last middle entry. Evaluating K1 at the all-ones vector bounds the bottom-six mass below by the top-three mass, giving (N-3)t<=1. When t<=1/(N+2), insert a copies of t. The ordered tuple retains its boundary and has mass 1+a*t and squared mass P+a*t^2. When t>=1/(N+2), remove only t, retaining the boundary and obtaining mass 1-t>0 and squared mass P-t^2. Positive normalization lets the endpoint bounds apply. The insertion quadratic lies below f(N) on the first interval; the deletion quadratic lies below f(N) between its roots 1/(N+2) and (N^2+15N+20)/((N^2+3N+8)(N+2)). For a cap (N-kappa)*t<=1 with N-kappa>0, the same scalar factorization places the cap below the second root when (10-kappa)*N^2+(6-15*kappa)*N-20*kappa-16>=0. Here kappa=3, and the guard is 7N^2-39N-76>=0 for N>=10. Zero values and ties are included. No preservation hypothesis is assumed. Application at length twenty: let F be the set of real p for which there exists l:Fin 20→R with l antitone, every l_i nonnegative, sum l_i=1, K1(boundaryValues 11 l) and K2(boundaryValues 11 l) positive semidefinite, and sum l_i^2=p. The retained DimensionTwentySpectralPurityBound.spectral_purity_bound, using the baseline lengths 18 and 21 and this same-delivery transfer through length 19, gives p<=7/121 for every p in F. Define e_i=3/22 when i=0 and e_i=1/22 otherwise. If i<=j and j=0, both indices are zero; if j is nonzero, its value is 1/22 and either possible value of e_i is at least that. Thus e is antitone, nonnegative, and its mass is (3+19)/22=1. Its observed nine-tuple is (3,1,1,1,1,1,1,1,1)/22. Both K1 and K2 are the matrix [[1,-1,0],[-1,1,0],[0,0,1]]/11. They are symmetric, and their quadratic form on every real x in R^3 is ((x0-x1)^2+x2^2)/11>=0, establishing positive semidefiniteness. Its square sum is (9+19)/22^2=7/121. Consequently 7/121 belongs to F and bounds F above: IsGreatest F (7/121), so its real supremum is also 7/121. This is the full attained-maximum application of the structural inequality, without a separate finite equality certificate or theorem. Feasibility of these two necessary boundary matrices alone does not assert literal APPT; physical realization and its universal-unitary proof are supplied separately in QuadbitQuintitMaximumPurity.", DescribeRole.Theorem),
            Desc("rankFourBoundaryIndex", "Six heads and ten tails",
                All("n",N,All("q",Fin(D(16)),Eqn(Call("rankFourBoundaryIndex",n,q),
                    Call("if",Seq(q,F.Lt,D(6)),q,Add(n,q))))),
                "In dimension n+16, the sixteen observed coordinates are the actual first six followed by the actual last ten. The remaining n coordinates form the middle. This observation includes boundary coincidences and zero coordinates.", DescribeRole.Definition),
            Desc("rankFourBoundaryValues", "Rank-four boundary observation",
                All("n",N,All("l",Vector(Add(n,D(16))),All("q",Fin(D(16)),
                    Eqn(Call("rankFourBoundaryValues",n,l,q),new Formula.Apply(l,[Call("rankFourBoundaryIndex",n,q)]))))),
                "The existing nine-coordinate qutrit observation is recovered by retaining slots 0,1,2,10,11,12,13,14,15. Thus both existing K1 and K2 act on exactly the same top three and bottom six coordinates as before. The rank-four mass condition compares the sum of slots 0 through 5 with that of slots 6 through 15.", DescribeRole.Definition),
            Desc("RankFourSpectralBound", "Bound under the rank-four necessary conditions",
                All("n",N,Seq(Call("RankFourSpectralBound",n),Iff,Sp,
                    All("l",Vector(Add(n,D(16))),Imp(And(
                        Feasible(Add(n,D(7)),l),
                        Le(Call("sumFirst",D(6),l),Call("sumLast",D(10),l))),
                        Le(Purity(Add(n,D(16)),l),Call("purityBound",Add(n,D(16)))))))),
                "The predicate universally quantifies all antitone nonnegative mass-one spectra of length n+16. It assumes both actual qutrit pencils are positive semidefinite and sumFirst 6 l <= sumLast 10 l. These are necessary spectral conditions. No APPT sufficiency, physical maximum, or uniqueness statement follows from the definition alone.", DescribeRole.Definition),
            Desc("rank_four_spectral_bound_transfer", "Rank-four dimension transfer",
                All("n",N,All("a",N,Imp(And(Le(D(8),n),Le(D(1),a),
                    Call("RankFourSpectralBound",n),Call("RankFourSpectralBound",Add(Add(n,D(1)),a))),
                    Call("RankFourSpectralBound",Add(n,D(1)))))),
                "Put N=n+17>=25 and t=l_(N-11), the actual coordinate immediately before the last ten. Inserting any positive number a of copies of t and deleting t preserve the first six and last ten coordinates, hence both actual qutrit pencils and the rank-four mass inequality. Order and nonnegativity are preserved even at ties and zeros. Ordering gives prefix mass at least (N-10)t and first-six mass at least 6t. The rank-four inequality therefore gives 1>=(N-4)t. In particular t<1, so deletion has positive mass. If t<=1/(N+2), insertion yields mass 1+at>0 and square sum P+at^2; the endpoint bound and the existing insertion factorization give P<=f(N+a)(1+at)^2-at^2<=f(N). If t>=1/(N+2), deletion yields mass 1-t and square sum P-t^2. The existing deletion factorization with kappa=4 gives f(N-1)(1-t)^2+t^2<=f(N). Its guard is 6(N^2-9N-16)>=0, which holds for N>=25; the cap is derived rather than postulated. Positive rescaling preserves the two pencils and the mass inequality. The theorem proves a new upper-bound implication between spectra in different dimensions; it does not assert that the necessary conditions characterize APPT.", DescribeRole.Theorem),
            Paragraph(Text("The four-slot audit of rank_four_spectral_bound_transfer remains declared_unresolved with source.selection_missing: the parameterized endpoint predicates require a shared dimension-indexed readout reconstruction that the current source selector does not supply. The concrete gap is recorded at https://github.com/the-omega-institute/trureturing/issues/19257. The audit of rank_four_endpoint_interval is declared_validated; the linked issue does not complete the local-transfer audit.")),
            Desc("rank_four_endpoint_interval", "An upper endpoint fills the finite interval",
                All("M",N,Imp(And(Le(D(8),X("M")),Call("RankFourSpectralBound",X("M"))),
                    All("n",N,Imp(And(Le(D(8),n),Le(n,X("M"))),Call("RankFourSpectralBound",n))))),
                "The length-24 base is obtained directly from QutritN8PurityBound.certificate_bound, which needs only the two qutrit pencils. Induction on n uses the rank-four dimension transfer with deletion endpoint n-1 and insertion count M-n. The top endpoint itself uses the supplied endpoint premise. Taking M=36 yields all actual dimensions 24<=N<=52 from the length-52 RankFourSpectralBound premise; N=n+16. The premise remains explicit. Physical application additionally requires the existing reduction from a literal unitary-quantified complex APPT density to one sorted spectrum satisfying these same necessary conditions. The published inner-polytope value and attainer remain attributed to Ahiable–Kothakonda–Winter, arXiv:2608.03390v2. No global uniqueness or literature-priority claim is made.", DescribeRole.Theorem))));
    }
}
