using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BanachGeometry;

internal sealed class LinfKNumberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/BanachGeometry/LinfKNumber.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/sainmannapaul2024local");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For real sup-norm spaces of dimension n ≥ 2, an extreme-point set is a K-set exactly when it spans, and the K-number is n.",
        H("K-sets and the K-number of real sup-norm spaces"),
        Blocks(
            Paragraph(Text("Sain, Manna and Paul, arXiv:2407.08900v1, Definition 1: “Definition 1. Let X be a Banach space. A set A ⊂ S_X is said to be a Koldobsky-set, for the sake of brevity, a K-set, if any operator T ∈ L(X) that preserves Birkhoff-James orthogonality at each point of A, is necessarily a scalar multiple of an isometry.”")),
            Paragraph(Text("Definition 3 of the same paper: “Definition 3. Let X be a Banach space having a finite K-set. Then the K-number of X is defined by min{|A| : A is a K-set of X}. We denote the K-number of X by κ(X).”")),
            Paragraph(Text("The Open Question at the end of §2 reads: “Open Question: Characterize the minimal K-sets in ℓ^n_∞ and hence find κ(ℓ^n_∞).” Minimal means minimal under inclusion. The characterization below concerns extreme-point sets; minimal K-sets containing non-extreme points are not classified.")),
            Entry("bj-orthogonality", "BJOrth", "Birkhoff–James orthogonality", Orthogonality(),
                "For a real seminormed space E, BJOrth x y requires that adding any real multiple of y cannot decrease the norm of x.",
                DescribeRole.Definition, true),
            Entry("local-preservation", "PreservesBJAt", "Preservation at a point", Preservation(),
                "PreservesBJAt T x means that for every y, x ⊥_B y ⇒ Tx ⊥_B Ty. The operator is real linear.",
                DescribeRole.Definition, true),
            Entry("scalar-isometry", "IsScalarMulIsometry", "A scalar multiple of an isometry", ScalarIsometry(),
                "The predicate states that one nonnegative real scalar c satisfies ‖T y‖ = c ‖y‖ for every y. It includes T = 0. For c > 0 on the finite-dimensional sup-norm carrier, dividing T by c gives a linear isometry; all linear endomorphisms of that carrier are bounded.",
                DescribeRole.Definition, true),
            Entry("k-set", "IsKSet", "Koldobsky sets", KSet(),
                "IsKSet A requires A to lie on the unit sphere and every real linear operator preserving Birkhoff–James orthogonality at every point of A to scale the norm. In the real finite-dimensional specialization this encodes Definition 1.",
                DescribeRole.Definition, true),
            Entry("k-number-claim", "claim", "The extreme-point characterization and cardinality bounds", Claim(),
                "Let X be Fin n → ℝ with the sup norm, V the extreme points of its closed unit ball, and n ≥ 2. The three conjuncts assert that every A ⊆ V is a K-set exactly when its real span is X, that an n-element K-set exists, and that every finite K-set has at least n elements. Together the last two give κ(X) = n under Definition 3. The extreme points are exactly the vectors with every coordinate of absolute value one. Their inclusion-minimal spanning subsets are exactly the bases contained in {±1}ⁿ.",
                DescribeRole.Definition, false),
            Entry("active-coordinate-descent", "active_not_BJ", "Strict descent at active coordinates",
                Disp(All("n", Nat, All("w", Call("Function", Call("Fin", V("n")), Real),
                    All("z", Call("Function", Call("Fin", V("n")), Real),
                        Imp(And(new Formula.Not(Eqn(V("w"), D(0))),
                            All("i", Call("Fin", V("n")),
                                Imp(Eqn(Call("abs", At(V("w"), V("i"))), Norm(V("w"))),
                                    new Formula.Relation(D(0), FormulaRelationOperator.LessThan,
                                        Mul(At(V("z"), V("i")), At(V("w"), V("i"))))))),
                            new Formula.Not(Call("BJOrth", V("w"), V("z")))))))),
                "For a nonzero finite real coordinate vector w, if zᵢwᵢ is strictly positive at every coordinate where |wᵢ| = ‖w‖, a sufficiently small negative multiple of z decreases every coordinate below ‖w‖. Finiteness gives one common step size. Therefore w is not Birkhoff–James orthogonal to z. This criterion controls the active facets in the image-vertex proof and in the polyhedral plane counterexample.",
                DescribeRole.Theorem, false),
            Entry("k-number-result", "result", "Proof of the characterization and the K-number", Disp(V("claim")),
                "At a vertex u, a zero coordinate of y implies u ⊥B y. A kernel vector contradicts preservation at a vertex with nonzero image, so a nonzero operator preserving at a spanning vertex set is injective. The active-coordinate inequality forces every coordinate of T u to have absolute value ‖T u‖. For S = T⁻¹, the proof gives uᵢ Sᵢⱼ (T u)ⱼ ≥ 0. Two nonzero entries in one column would constrain all test vertices to uᵢ = ±uₖ, contradicting span. Thus S has permutation support, and its action on one vertex fixes the common absolute value of its nonzero entries. This proves norm scaling. Conversely a nonzero rank-one operator annihilating a proper span preserves at that set but cannot scale the norm in dimension at least two. Finally, the all-ones vector and the n − 1 vectors obtained by changing one nonzero-index coordinate to −1 form an n-element spanning vertex set. The characterization also implies that any n linearly independent extreme points suffice in these sup-norm spaces.",
                DescribeRole.Theorem, false,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sain-manna-paul-2024-linf-k-number"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equivalence(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula SubsetOf(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula LinearEndo(Formula e) => Call("LinearMap", Real, e, e);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);

    private static Formula Orthogonality() => Disp(Equivalence(
        Call("BJOrth", V("x"), V("y")),
        All("t", Real, Leq(Norm(V("x")), Norm(Add(V("x"), Mul(V("t"), V("y"))))))));

    private static Formula Preservation() => Disp(Equivalence(
        Call("PreservesBJAt", V("T"), V("x")),
        All("y", V("E"), Imp(Call("BJOrth", V("x"), V("y")),
            Call("BJOrth", At(V("T"), V("x")), At(V("T"), V("y")))))));

    private static Formula ScalarIsometry() => Disp(Equivalence(
        Call("IsScalarMulIsometry", V("T")),
        Some("c", Real, And(Leq(D(0), V("c")),
            All("y", V("E"), Eqn(Norm(At(V("T"), V("y"))), Mul(V("c"), Norm(V("y")))))))));

    private static Formula PreservesOn(Formula a) => All("x", V("E"),
        Imp(Member(V("x"), a), Call("PreservesBJAt", V("T"), V("x"))));

    private static Formula KSet() => Disp(Equivalence(Call("IsKSet", V("A")),
        And(SubsetOf(V("A"), Call("sphere", D(0), D(1))),
            All("T", LinearEndo(V("E")), Imp(PreservesOn(V("A")),
                Call("IsScalarMulIsometry", V("T")))))));

    private static Formula Claim()
    {
        Formula x = Seq(Call("Fin", V("n")), Sp, To, Sp, Real);
        Formula vertices = Call("extremePoints", Real, Call("closedBall", D(0), D(1)));
        Formula characterization = All("A", Call("Set", x),
            Imp(SubsetOf(V("A"), vertices),
                Equivalence(Call("IsKSet", V("A")), Eqn(Call("span", Real, V("A")), Call("top")))));
        Formula finite = Call("Finset", x);
        Formula asSet = Call("coe", V("A"));
        Formula existence = Some("A", finite,
            And(Eqn(Call("card", V("A")), V("n")), Call("IsKSet", asSet)));
        Formula bound = All("A", finite,
            Imp(Call("IsKSet", asSet), Leq(V("n"), Call("card", V("A")))));
        return Disp(Equivalence(V("claim"), All("n", Nat, Imp(Leq(D(2), V("n")),
            And(characterization, And(existence, bound))))));
    }
}
