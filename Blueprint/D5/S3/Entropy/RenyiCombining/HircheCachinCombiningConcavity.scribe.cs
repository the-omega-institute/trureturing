using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.RenyiCombining;

internal sealed class HircheCachinCombiningConcavityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/hirche2020renyibounds");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hirche Conjecture IV.18 holds with threshold five quarters, including the Shannon order and all entropy endpoints.",
        H("Hirche's Binary Renyi Information Combining Conjecture"),
        Blocks(
            Paragraph(Text("The source assertion is the whole of Conjecture IV.18 of C. Hirche, "
                + "Renyi Bounds on Information Combining, ISIT 2020, arXiv:2004.14408v1, Conjecture IV.18. "
                + "The logarithm is natural, so the entropy interval is [0,log 2]. "
                + "The parameter alpha is real; it is not restricted to integers. The formal claim fixes any second entropy coordinate "
                + "in the entire closed interval and proves convexity for 0 < alpha < 5/4 and concavity for alpha >= 2. "
                + "The threshold witness is alphaHat = 5/4.")),
            Paragraph(Text("Conjecture IV.18 states: There exists a value 1 < α̂ < 1.3863, such that "
                + "hα(hα⁻¹(x) ∗ hα⁻¹(y)) is convex for 0 < α < α̂ and concave for α ≥ 2.")),
            Node("h", "Binary Renyi entropy", AllReal("alpha", AllReal("p",
                Equal(Call("h", N("alpha"), N("p")), Call("ite", Equal(N("alpha"), D(1)),
                    Call("binEntropy", N("p")), new Formula.Fraction(
                    Call("log", Add(Pow(N("p"), N("alpha")),
                        Pow(Subtract(D(1), N("p")), N("alpha")))),
                    Subtract(D(1), N("alpha"))))))), DescribeRole.Definition,
                "At alpha = 1 the definition uses Real.binEntropy in natural-log units; otherwise both variable powers use Real.rpow. On the probability branch [0,1/2], for every alpha > 0, "
                + "the power sum is positive and h is continuous and strictly increasing, with values zero at zero and log 2 at one half. "
                + "The displayed total real definition also exists outside the parameter and probability domain of the theorem."),
            Node("hInv", "The specified inverse branch", AllReal("alpha", AllReal("x",
                Equal(Call("hInv", N("alpha"), N("x")),
                    Call("invFunOn", Call("h", N("alpha")), Interval("Icc", D(0), Half()), N("x"))))),
                DescribeRole.Definition,
                "This is Function.invFunOn applied to h alpha on the closed interval [0,1/2]. "
                + "For alpha > 0, that restriction is a continuous strictly increasing bijection onto [0,log 2]. "
                + "Consequently, for x in the entropy interval, hInv(alpha,x) belongs to [0,1/2] and h(alpha,hInv(alpha,x))=x. "
                + "The inverse is continuous on the entropy interval. No inverse identity outside that interval is claimed."),
            Node("star", "Binary convolution", AllReal("a", AllReal("b",
                Equal(Call("star", N("a"), N("b")), Subtract(Add(N("a"), N("b")),
                    Multiply(Multiply(D(2), N("a")), N("b")))))), DescribeRole.Definition,
                "For binary error probabilities a and b, star(a,b)=a+b-2ab is their binary convolution."),
            Node("G", "Entropy-coordinate combining map", AllReal("alpha", AllReal("x", AllReal("y",
                Equal(Call("G", N("alpha"), N("x"), N("y")), Call("h", N("alpha"),
                    Call("star", Call("hInv", N("alpha"), N("x")),
                        Call("hInv", N("alpha"), N("y")))))))), DescribeRole.Definition,
                "G evaluates the binary entropy after convolving the two specified inverse-branch probabilities."),
            Node("claim", "The complete threshold conjecture", Equal(N("claim"), ClaimBody()),
                DescribeRole.Definition,
                "The existential threshold is strictly between one and 13863/10000. The convex clause quantifies over "
                + "all positive real orders below it, and the concave clause over all real orders at least two. "
                + "Both clauses use Mathlib's full two-point inequality on the closed entropy interval, including both endpoints."),
            Node("result", "Hirche Conjecture IV.18 with threshold five quarters", ClaimBody(), DescribeRole.Theorem,
                "The witness 5/4 lies strictly between 1 and 1.3863. For every y in [0,log 2], x maps to G(alpha,x,y) "
                + "is convex for every 0 < alpha < 5/4 and concave for every alpha >= 2. "
                + "Symmetry of binary convolution also gives the corresponding second-coordinate statement as a mathematical consequence; "
                + "the Lean result has exactly the displayed first-coordinate claim.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hirche-2020-cachin-renyi-information-combining-convexity"), ResolutionKind.Proved)),
            Paragraph(Text("Set psi(t)=h(alpha,(1-t)/2) and f(t)=-psi'(t) for 0<t<1. "
                + "The function f is positive, and psi decreases continuously from log 2 to zero on [0,1]. "
                + "The inverse bias is t(x)=1-2hInv(alpha,x), so psi(t(x))=x. "
                + "Binary convolution gives G(alpha,x,y)=psi(v t(x)), where v=t(y) belongs to [0,1].")),
            Paragraph(Text("For alpha >= 2, set n=alpha-1 and r=(1-t)/(1+t). Then the certificate transform T=(1-r^n)/(1+r^n) gives "
                + "f(t)=(alpha/n)T/(1+tT). Its derivative satisfies f'(t)=f(t)F(n,r)/t. "
                + "The certificate proves that r maps to F(n,r) is nondecreasing for n>=1. Since r decreases with t, "
                + "the elasticity E(t)=F(n,r(t)) is nonincreasing.")),
            Paragraph(Text("Fix 0<v<1. Differentiation gives the entropy-coordinate derivative R(t)=v f(vt)/f(t). "
                + "Its t derivative is v f(vt)[E(vt)-E(t)]/[t f(t)], which is nonnegative because vt<=t and E is nonincreasing. "
                + "The inverse bias decreases with x. Thus the derivative of x maps to psi(v t(x)) is antitone in x, "
                + "and Mathlib's derivative criterion yields concavity on the closed interval using continuity there. "
                + "Only interior inverse derivatives are used.")),
            Paragraph(Text("At v=0 the transported function is constant, and at v=1 it is the identity. "
                + "These two cases include the endpoint values of y. The proof therefore covers both closed-coordinate boundaries "
                + "without endpoint inverse derivatives. For 0 < alpha < 1 the negative-n certificate gives the opposite "
                + "elasticity sign. At alpha = 1 the binary Shannon entropy derivative is minus artanh(t), with strictly "
                + "increasing elasticity t/((1-t^2)artanh(t)). For 1 < alpha <= 5/4, put n=alpha-1 and "
                + "C(z)=n sqrt(z) coth(n artanh(sqrt(z))), D(z)=C(z)+nz. The desingularized even analytic quotient "
                + "supplies the initial first and second derivative signs. The Riccati identity and its differentiated "
                + "equation preclude a first zero of C'', and imply D'<0. Thus "
                + "1-2zD'/D is strictly increasing. This reverses the slope-ratio sign and yields closed-interval convexity.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hirche-combining-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            (name == "result" || name == "convexOn_G_of_le_one") ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);
    private static Formula N(string value) => F.Id(value);
    private static Formula RealType() => Seq(Mathbb, Grp(N("R")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Half() => new Formula.Fraction(D(1), D(2));
    private static Formula AllReal(string name, Formula body) =>
        Seq(Forall, Sp, Par(Seq(N(name), Colon, Sp, RealType())), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Par(premise), FormulaLogicOperator.Implies, conclusion);
    private static Formula Rel(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(Par(value), exponent);
    private static Formula Interval(string name, Formula left, Formula right) => Call(name, left, right);
    private static Formula EntropyInterval() => Interval("Icc", D(0), Call("log", D(2)));
    private static Formula ConcaveBody() => AllReal("alpha",
        Imp(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, N("alpha")), AllReal("y",
            Imp(Rel(N("y"), FormulaRelationOperator.MemberOf, EntropyInterval()),
                Call("ConcaveOn", RealType(), EntropyInterval(),
                    Par(Seq(N("x"), Sp, Mapsto, Sp, Call("G", N("alpha"), N("x"), N("y")))))))));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula ConvexBody() => AllReal("alpha",
        Imp(Rel(D(0), FormulaRelationOperator.LessThan, N("alpha")),
            Imp(Rel(N("alpha"), FormulaRelationOperator.LessThan, N("alphaHat")), AllReal("y",
                Imp(Rel(N("y"), FormulaRelationOperator.MemberOf, EntropyInterval()),
                    Call("ConvexOn", RealType(), EntropyInterval(),
                        Par(Seq(N("x"), Sp, Mapsto, Sp, Call("G", N("alpha"), N("x"), N("y"))))))))));
    private static Formula ClaimBody() => Seq(Exists, Sp,
        Par(Seq(N("alphaHat"), Colon, Sp, RealType())), Comma, Sp,
        And(Rel(D(1), FormulaRelationOperator.LessThan, N("alphaHat")),
            And(Rel(N("alphaHat"), FormulaRelationOperator.LessThan,
                new Formula.Fraction(D(1,3,8,6,3), D(1,0,0,0,0))), And(Par(ConvexBody()), Par(ConcaveBody())))));

}
