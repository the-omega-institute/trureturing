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
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp, y);
    private static Formula Imp(Formula p, Formula q) => Seq(Par(p), Rightarrow, Par(q));
    private static Formula And(params Formula[] fs) => Seq(fs.SelectMany((f,i) => i == 0 ? new[] {Par(f)} : new[] {Land, Par(f)}).ToArray());
    private static Formula All(string n, Formula t, Formula f) => Seq(Forall, Par(Seq(X(n), Colon, t)), Comma, Par(f));
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
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
        var p=X("p"); var dim=X("N"); var k=X("kappa"); var c=X("C");
        Formula Bound(Formula z) => Call("ObserverBound",p,q,c,z);
        var actualObservation=Call("observerValues",p,q,dim,l);
        var feasible=And(Call("Antitone",l),
            All("i",Fin(dim),Le(D(0),Call("l",X("i")))),
            Eqn(Mass(dim,l),D(1)),Call("C",actualObservation));
        var cap=All("l",Vector(dim),Imp(feasible,
            Le(Call("multiply",Sub(dim,k),Call("l",Sub(Sub(dim,q),D(1)))),D(1))));
        var guard=Sub(Sub(Add(Call("multiply",Sub(D(10),k),Sq(dim)),
            Call("multiply",Sub(D(6),Call("multiply",D(15),k)),dim)),
            Call("multiply",D(20),k)),D(16));
        var hypotheses=And(Eqn(dim,Add(Add(Add(p,q),n),D(1))),Le(D(10),dim),Le(D(1),a),
            Call("PositiveScaleInvariant",c),Seq(D(1),F.Lt,Sub(dim,k)),Le(D(0),guard),cap);
        var transferFormula=All("p",N,All("q",N,All("n",N,All("a",N,All("N",N,
            All("C",Arrow(Vector(Add(p,q)),X("Prop")),All("kappa",R,
                Imp(hypotheses,Imp(Bound(Sub(dim,D(1))),Imp(Bound(Add(dim,a)),Bound(dim)))))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual extremal observers transfer spectral bounds across dimensions.",
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
                All("n",N,Seq(Call("SpectralBound",n),Iff,All("l",Vector(Add(n,D(9))),
                    Imp(Feasible(n,l),Le(Purity(Add(n,D(9)),l),Call("purityBound",Add(n,D(9)))))))),
                "SpectralBound n is the universal square-sum upper bound for all antitone nonnegative mass-one vectors of length n+9 whose two boundary pencils are positive semidefinite. This is a spectral relaxation; no sufficiency assertion for literal APPT is included.", DescribeRole.Definition),
            Desc("observerIndex", "Actual extremal coordinate indices",
                All("p",N,All("q",N,All("N",N,Imp(Le(Add(X("p"),q),X("N")),
                    All("i",Fin(Add(X("p"),q)),Eqn(Call("observerIndex",X("p"),q,X("N"),X("i")),
                        Call("if",Seq(X("i"),F.Lt,X("p")),X("i"),
                            Add(Sub(X("N"),Add(X("p"),q)),X("i"))))))))),
                "For p+q<=N, this index selects the actual first p and last q coordinates, in that order. The subtraction is on natural indices under the displayed size hypothesis. It does not discard ties or require strict ordering.", DescribeRole.Definition),
            Desc("observerValues", "The top and bottom observation",
                All("p",N,All("q",N,All("N",N,Imp(Le(Add(X("p"),q),X("N")),
                    All("l",Vector(X("N")),Eqn(Call("observerValues",X("p"),q,X("N"),l),
                        Call("compose",l,Call("observerIndex",X("p"),q,X("N"))))))))),
                "The observer is the original extremal tuple, indexed by Fin(p+q). Its proof argument records p+q<=N. Positive division commutes with observation.", DescribeRole.Definition),
            Desc("PositiveScaleInvariant", "Faithful positive normalization",
                Seq(Call("PositiveScaleInvariant",X("C")),Iff,
                    All("b",Vector(X("d")),All("s",R,Imp(Seq(D(0),F.Lt,X("s")),
                        Seq(Call("C",Call("divide",X("b"),X("s"))),Iff,Sp,Call("C",X("b"))))))),
                "The boundary condition is preserved in both directions by division by every positive real mass. This is a hypothesis of the shared theorem, separately established for each concrete boundary condition.", DescribeRole.Definition),
            Desc("ObserverBound", "A universal bound for an extremal observer",
                Seq(Call("ObserverBound",X("p"),q,X("C"),X("N")),Iff,
                    Imp(Le(Add(X("p"),q),X("N")),All("l",Vector(X("N")),
                        Imp(And(Call("Antitone",l),All("i",Fin(X("N")),Le(D(0),Call("l",X("i")))),
                            Eqn(Mass(X("N"),l),D(1)),Call("C",Call("observerValues",X("p"),q,X("N"),l))),
                            Le(Purity(X("N"),l),Call("purityBound",X("N"))))))),
                "Every antitone, nonnegative, mass-one spectrum whose actual top-p/bottom-q observer satisfies C has the stated purity bound. The size-proof quantifier is explicit in Lean; at dimensions below p+q this predicate carries no conclusion about spectra.", DescribeRole.Definition),
            Desc("observer_bound_transfer", "Transfer through the actual unobserved coordinate",
                transferFormula,
                "Here N=p+q+n+1, with N>=10 and a>=1. Kappa is real, and guard(N,kappa)=(10-kappa)N^2+(6-15kappa)N-20kappa-16 must be nonnegative, with N-kappa>1. The cap is required for every feasible spectrum at the current dimension. The actual coordinate j=N-q-1 has value t. Inserting a actual copies immediately before j preserves the observed entries, weak order and nonnegativity, with exact mass 1+a*t and squared mass P+a*t^2. Deleting exactly the original coordinate j preserves the observer, with exact mass 1-t and squared mass P-t^2. Both masses are positive in their respective scalar branches. Normalization then uses the same boundary predicate C. The insertion branch uses t<=1/(N+2); the deletion branch uses the opposite inequality and the full guard. No assertion for arbitrary observers without the cap and guards is included. If bottom-q mass is at least top-p mass, order and total mass give (N+p-q)t<=1, so kappa=q-p is a real difference, without saturated natural subtraction. The rank-three specialization p=3,q=6 derives this balance from K1 and retains its original complete theorem and length-twenty application. For the augmented rank-four observer p=6,q=10, select positions 0,1,2,10,11,12,13,14,15 to obtain exactly the original K1 and K2, and additionally impose L4=bottom-ten mass minus top-six mass>=0. The selection commutes with positive division, and L4 scales by the same positive factor. These are exactly the two original pencils and this one balance inequality, with no extra LMIs or rank restrictions. This balance gives (N-4)t<=1 with actual t=l[N-11]. At N>=17, N-4>1 and the guard 6N^2-54N-96>=0 hold, so this precise augmented predicate transfers from N-1 and N+a to N. H28 means the universal augmented bound over ALL such length-28 spectra, at 1/25; it remains an undischarged hypothesis. The length-24 spectral certificate can supply the left endpoint by forgetting L4; its physical 3x8 consequence alone is not that universal spectral statement. With both spectral endpoints supplied, the N=25,a=3 consequence is conditional and has value 11/243. It is not a physical 5x5 acceptance statement; dimensions 26 and 27 are auxiliary dimensions.", DescribeRole.Theorem),
            Desc("spectral_bound_transfer", "Transfer from two endpoint dimensions",
                All("n",N,All("a",N,Imp(Le(D(1),a),Imp(Call("SpectralBound",n),
                    Imp(Call("SpectralBound",Add(Add(n,D(1)),a)),Call("SpectralBound",Add(n,D(1)))))))),
                "Put N=n+10 and let t be the actual last middle entry. Evaluating K1 at the all-ones vector bounds the bottom-six mass below by the top-three mass, giving (N-3)t<=1. When t<=1/(N+2), insert a copies of t. The ordered tuple retains its boundary and has mass 1+a*t and squared mass P+a*t^2. When t>=1/(N+2), remove only t, retaining the boundary and obtaining mass 1-t>0 and squared mass P-t^2. Positive normalization lets the endpoint bounds apply. The insertion quadratic lies below f(N) on the first interval; the deletion quadratic lies below f(N) between its roots 1/(N+2) and (N^2+15N+20)/((N^2+3N+8)(N+2)). For a cap (N-kappa)*t<=1 with N-kappa>1, the same scalar factorization places the cap below the second root when (10-kappa)*N^2+(6-15*kappa)*N-20*kappa-16>=0. Here kappa=3, and the guard is 7N^2-39N-76>=0 for N>=10. Zero values and ties are included. No preservation hypothesis is assumed.", DescribeRole.Theorem))));
    }
}
