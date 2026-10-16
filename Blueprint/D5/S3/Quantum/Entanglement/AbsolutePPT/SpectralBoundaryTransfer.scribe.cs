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
            "Rank-three spectral bounds transfer across arbitrary middle multiplicities.",
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
                "Natural dimensions are cast to the reals before division. The candidate value is f(N)=(N+8)/(N+2)^2.", DescribeRole.Definition),
            Desc("SpectralBound", "A bound for the rank-three relaxation",
                All("n",N,Seq(Call("SpectralBound",n),Iff, Sp,All("l",Vector(Add(n,D(9))),
                    Imp(Feasible(n,l),Le(Purity(Add(n,D(9)),l),Call("purityBound",Add(n,D(9)))))))),
                "SpectralBound n is the universal square-sum upper bound for all antitone nonnegative mass-one vectors of length n+9 whose two boundary pencils are positive semidefinite. This is a spectral relaxation; no sufficiency assertion for literal APPT is included.", DescribeRole.Definition),
            Desc("spectral_bound_transfer", "Transfer from two endpoint dimensions",
                All("n",N,All("a",N,Imp(Le(D(1),a),Imp(Call("SpectralBound",n),
                    Imp(Call("SpectralBound",Add(Add(n,D(1)),a)),Call("SpectralBound",Add(n,D(1)))))))),
                "Put N=n+10 and let t be the actual last middle entry. Evaluating K1 at the all-ones vector bounds the bottom-six mass below by the top-three mass, giving (N-3)t<=1. When t<=1/(N+2), insert a copies of t. The ordered tuple retains its boundary and has mass 1+a*t and squared mass P+a*t^2. When t>=1/(N+2), remove only t, retaining the boundary and obtaining mass 1-t>0 and squared mass P-t^2. Positive normalization lets the endpoint bounds apply. The insertion quadratic lies below f(N) on the first interval; the deletion quadratic lies below f(N) between its roots 1/(N+2) and (N^2+15N+20)/((N^2+3N+8)(N+2)). For a cap (N-kappa)*t<=1 with N-kappa>0, the same scalar factorization places the cap below the second root when (10-kappa)*N^2+(6-15*kappa)*N-20*kappa-16>=0. Here kappa=3, and the guard is 7N^2-39N-76>=0 for N>=10. Zero values and ties are included. No preservation hypothesis is assumed.", DescribeRole.Theorem))));
    }
}
