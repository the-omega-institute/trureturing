using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class RationalIntervalRetractionDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => Seq(Id(s), Open,
        new Formula.LatexSequence([.. xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x })]), Close);
    private static Formula Pow(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula Fr(int n, int d) => Seq(Frac, Grp(Num(n)), Grp(Num(d)));
    private static Formula St(params Formula[] xs) => Disp(new Formula.Aligned([.. xs]));
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), InMacro, Sp, t, Comma, Sp);
    private static Formula ZZ => Seq(Mathbb, Grp(Id("Z")));
    private static Formula NN => Seq(Mathbb, Grp(Id("N")));
    private static Formula Pg(Formula g) => Seq(Id("P"), Underscore, Grp(g));
    private static Formula X(Formula k) => Call("x", k);
    private static Formula Shift => Call("shift", Id("l"), Id("x"));
    private static Formula Rof(Formula x) => Call("R", x);
    private static Formula E => Call("E", Id("x"), Id("k"));
    private static Formula Tail => Seq(Lim, Underscore, Grp(Bar, Id("k"), Bar, To, Sp, Infty));
    private static DocumentBlock.Describe Desc(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("rational-retraction-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/RationalIntervalRetraction." + name), H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/artigue2025shadowing")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit finite weighted orbit retraction is continuous on the entire closed interval pseudo-orbit domain, including both empty caps.",
        H("Rational Interval Orbit Retraction"), Blocks(
        Paragraph(Text("Let I=[0,1], f(u)=2u/(1+u), delta=1/256, and P=P_delta. For any real gamma, P_gamma consists of all x:Z->I with "
            + "|f(x(k))-x(k+1)|<=gamma at every integer k, with the product subtype topology. These are the closed bi-infinite domains of Artigue, Shadowing maps, Section 2.1. "
            + "This rational construction is separate from the cited paper. Write shift(l,x)(k)=x(l+k) and O(p)(k)=f^k(p).")),
        Paragraph(Text("The actual weight is w(u)=max(0,(u-1/3)(2/3-u)), and g(u)=w(u)u/max(1/3,1-u). The continuous extension g is zero off the open middle band and equals w(u)u/(1-u) on it. "
            + "Let B(x)={k:1/3<x(k)<2/3}. The marker classification gives a finite consecutive set of at most three indices. Define W(x) as the sum of w(x(k)) and A(x) as the sum of 2^(-k)g(x(k)) over all integers; "
            + "their supports are finite. W(x)>0 exactly when B(x) is nonempty. For Q(s)=s/(1+s), set R(x)=Q(A(x)/W(x)) in that case. If B(x) is empty, the entire sequence lies strictly in one cap; R(x) is zero on the lower cap and one on the upper cap.")),
        Desc("R_lower_cylinder", "Lower cap cylinder estimate",
            St(Seq(All("x", Id("P")), All("j", ZZ), X(Id("j")), Lt, Fr(1,2), Rightarrow, Sp,
                Rof(Id("x")), Le, Sp, D(8), Cdot, Sp, Pow(D(2), Seq(Minus, Id("j"))))),
            "For a nonempty marker block [a,b], the quotient lies between 2^(-b)/2 and 2*2^(-a). The coordinate condition forces b>=j and hence a>=j-2. "
                + "Thus Q(A/W)<=A/W<=8*2^(-j). Empty-marker sequences in this cylinder are in the lower cap."),
        Desc("R_upper_cylinder", "Upper cap cylinder estimate",
            St(Seq(All("x", Id("P")), All("j", ZZ), Fr(1,2), Lt, X(Id("j")), Rightarrow, Sp,
                D(1), Minus, Rof(Id("x")), Le, Sp, D(8), Cdot, Sp, Pow(D(2), Id("j")))),
            "The coordinate condition forces a<=j and b<=j+2, so A/W>=2^(-j-2)/2. Then 1-Q(A/W)=1/(1+A/W)<=8*2^j. "
                + "Empty-marker sequences in this cylinder are in the upper cap."),
        Desc("continuous_R", "Continuity on the entire closed domain",
            St(Seq(Operatorname, Grp(Id("Continuous")), Open, Id("R"), Colon, Id("P"), To, Sp, Id("I"), Close)),
            "At a point with marker j, keeping its weight positive confines every neighboring marker to [j-2,j+2]. The numerator and denominator are then fixed finite coordinate sums and the denominator is positive. "
                + "At every empty lower-cap sequence, a cylinder at a sufficiently large positive j makes the lower estimate arbitrarily small. At every empty upper-cap sequence, use a sufficiently negative j and the upper estimate. "
                + "This covers nonconstant empty-cap sequences and the appearance or disappearance of boundary markers. No global continuity of W or uniform positive lower bound on W is asserted."),
        Desc("W_shift", "Integer reindexing of the weight sum",
            St(Seq(All("x", Id("P")), All("l", ZZ), Call("W", Shift), Eq, Call("W", Id("x")))),
            "Translation is a bijection of the integer index set, so it preserves the finite weight sum."),
        Desc("A_shift", "Integer reindexing of the phase numerator",
            St(Seq(All("x", Id("P")), All("l", ZZ), Call("A", Shift), Eq, Pow(D(2), Id("l")), Call("A", Id("x")))),
            "The exact identity 2^(-k)=2^l*2^(-(l+k)) supplies the phase factor under the same reindexing."),
        Desc("R_shift", "Exact equivariance at every integer time",
            St(Seq(All("x", Id("P")), All("l", ZZ), Rof(Shift), Eq, Pow(Id("f"), Id("l")), Open, Rof(Id("x")), Close)),
            "For nonempty marker sets the quotient scales by 2^l, and Q(2^l s)=H(2^l)(Q(s)). Empty marker sets retain their cap under translation, and both endpoints are fixed. "
                + "The proof establishes one-step equivariance directly and uses the existing homeomorphism-group integer equivariance theorem for every positive and negative l."),
        Desc("R_trueOrbit", "Fixing all genuine orbits",
            St(Seq(All("p", Id("I")), Rof(Call("O", Id("p"))), Eq, Id("p"))),
            "Both endpoint orbits have empty markers and are fixed by their cap value. For an interior p, the negative orbit limit is zero and the positive orbit limit is one, so the orbit cannot lie wholly in either cap and must have a marker. "
                + "At every marker k, 2^(-k) times the odds of f^k(p) equals p/(1-p). The finite weighted sum therefore gives A/W=p/(1-p), and Q(A/W)=p."),
        Paragraph(Text("For the following statement define e(x,k)=dist(x(k+1),f(x(k))) and E(x,k)=dist(f^k(R(x)),x(k)). Inclusion from P_gamma into P is literal sequence inclusion. "
            + "For x in P_gamma the expression R(x) in E means evaluation after that inclusion. Limits as |k| tends to infinity are the cofinite filter on Z.")),
        Desc("R_global_and_limit_shadowing", "One explicit map at all accuracies and both infinite tails",
            St(
                Seq(Open, Forall, Sp, Varepsilon, Gt, D(0), Comma, Sp,
                    Exists, Sp, GammaLower, Gt, D(0), Comma, Sp, GammaLower, Le, Sp, Fr(1,256), Land, Sp,
                    All("x", Pg(GammaLower)), All("k", ZZ), E, Lt, Varepsilon, Close, Land),
                Seq(Open, All("x", Id("P")), Tail, Call("e", Id("x"), Id("k")), Eq, D(0), Rightarrow),
                Seq(Open, Forall, Sp, Varepsilon, Gt, D(0), Comma, Sp, Exists, Sp, Id("N"), InMacro, Sp, NN, Comma, Sp,
                    All("k", ZZ), Id("N"), Le, Sp, Bar, Id("k"), Bar, Rightarrow, Sp, E, Lt, Varepsilon, Close, Land),
                Seq(Tail, E, Eq, D(0), Close)),
            "Apply CompactSelector.global_and_limit_shadowing to this fixed R, its continuity, true-orbit identity and exact one-step equivariance. "
                + "The first conclusion is uniform over all integer centers after shrinking the closed error scale. The second holds on the full fixed P and imposes no finite-support or eventual-exactness condition on the link errors. "
                + "The natural tail bound and the cofinite limit are both included. This establishes the selector and its global and two-sided limit shadowing. The phase-memory map T and its every-rho failure of self-tuning are separate further conclusions.")
        )));
}
