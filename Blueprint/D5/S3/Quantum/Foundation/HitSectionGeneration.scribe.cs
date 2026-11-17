using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class HitSectionGenerationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual pure-pair face incidence preserves the original pure generators of every containing linear section.",
        H("Pure generators of original linear sections"),
        Blocks(
            Paragraph(Text("The original carrier is a finite dimensional real normed vector space V. C is the original closed convex cone containing zero, and u is the original real linear unit, strictly positive at every nonzero vector of C. K is the entire normalized base and P is its entire extreme-point set, as defined by CircuitBalancedConfirmation. The source domain also requires a nonzero carrier and a pointed generating cone; the proof establishes the result without needing those additional restrictions. Neither the set of pure points nor a minimal face is assumed closed. No finite-pure, ball, L2, NC, SP, ROG or PSD premise is introduced.")),
            Entry("neighbors", "neighbors", "All originally distinguishable pure neighbours",
                "For each a in V, neighbors(C,u,a) is exactly the intersection of the entire original pure set with FacetZeroGluing.exclusion(C,u,a). Thus b is an original pure point and one original real linear effect f satisfies 0 <= f(c) <= u(c) for every c in C, f(a)=1 and f(b)=0. The two readings belong to the same original effect; there is no supplied zero-face or chosen pure subconfiguration.", DescribeRole.Definition),
            Entry("hit", "Hit", "Incidence with every actual pure-pair face",
                "For every pair p,q in the complete original pure subtype, p != q implies that neighbors(C,u,a) meets WholePairBallConfirmation.pairBase(C,u,p,q). pairBase is the whole normalized slice of the smallest original cone face containing both points: membership is tested against every native cone face containing p and q. The original strict unit and base_face_lift identify this with the actual minimal convex face of K, without changing the face to its closure.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-pure-generation"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/HitSectionGeneration.base_eq_convexHull_pure"),
                H("Finite pure generation without a closed pure set"),
                StatementSource.FromAuthor(Disp(Telescope(Implies(Hypotheses(),
                    Equal(Base(), Hull(Pure())))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original C,u with C closed and u strictly positive on its nonzero elements, the whole base K equals the ordinary real convex hull of all its extreme points. The convex hull is finite, with no closure operation. The assertion includes an empty base and a singleton base. This theorem is consumed by hit_section_generation on both the principal face and the section cone.")),
                    Paragraph(Text("For each x in K the proof constructs the native principal face consisting of all y in C for which t*x-y is in C for some nonnegative real t. It contains x. A native cone face equals C intersect its real linear span by the original face_span_inter; finite dimension and closedness of C therefore make this particular face closed. Its normalized base is compact by base_compact. Krein-Milman is used in its exact pinned form with closure. Choose a point y in the intrinsic interior of the convex hull of the face's extreme points. Positive domination explicitly extends the line from y through the designated x within the same face. The pinned open-segment intrinsic-interior theorem then puts x in the ordinary convex hull. Extreme points of the face base are original extreme points. This supplies finite pure generation without assuming it as a premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-section-conclusions"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/HitSectionGeneration.hit_section_generation"),
                H("All pure and finite conic generators of a hit section"),
                StatementSource.FromAuthor(Disp(Telescope(
                    All("a", Pure(), All("S", Call("Submodule", Real(), F.Id("V")),
                        Implies(And(Hypotheses(), And(Call("Hit", F.Id("C"), F.Id("u"), F.Id("a")),
                            new Formula.Relation(Call("neighbors", F.Id("C"), F.Id("u"), F.Id("a")),
                                FormulaRelationOperator.SubsetOf, F.Id("S")))),
                            And(Equal(Call("extremePoints", Real(), Section()), PureSection()),
                                And(Equal(Section(), Hull(PureSection())),
                                    Equal(Call("inter", F.Id("C"), F.Id("S")),
                                        Call("PointedConeHull", Real(), PureSection())))))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original pure a satisfying Hit and every real linear subspace S containing all original neighbours of a, the extreme points of K intersect S are exactly P intersect S, K intersect S is the ordinary real convex hull of P intersect S, and C intersect S is PointedCone.hull over the reals of P intersect S. PointedCone.hull is the nonnegative-scalar submodule span, equivalently all finite nonnegative sums; it includes zero. Empty sections and singleton bases remain in scope.")),
                    Paragraph(Text("If a section extreme x were not an original pure point, the compact normalized principal face of x has two distinct extreme points p,q. They are original pure points. Hit produces an original pure neighbour b in the actual pair face, hence in the principal face and in S. The explicit positive-domination extension gives z in the same principal face with x in the open segment from b to z. Linearity of S puts z in S. Section extremeness forces b=x, contradicting the nonpurity of x. The reverse extreme-point inclusion is restriction to a subset. Apply finite pure generation to C intersect S for the second conclusion. For the third, normalize every nonzero c by the same original positive u(c), then rescale its finite convex decomposition. The zero case is retained separately.")),
                    Paragraph(Text("The source is Quantum Origin Binary Normal Differences and Orientation XVII, section 197.2, Theorem 197.3. The first result supplies a mature convex-geometric prerequisite; the new incidence argument connects actual face hitting with preservation of the original section generators. Sections 197.3 and the finite-cone argument following it are source applications, not claimed existing Lean consumers. No classification, reconstruction, physical implementation, literature priority, frozen membership or atom coverage follows merely from these declarations."))), DescribeRole.Theorem))));

    private static DocumentBlock.Describe Entry(string id, string declaration, string title,
        string text, DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create("D5/S3/Quantum/Foundation/HitSectionGeneration." + declaration),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Base() => Call("base", F.Id("C"), F.Id("u"));
    private static Formula Pure() => Call("pure", F.Id("C"), F.Id("u"));
    private static Formula Hull(Formula s) => Call("convexHull", Real(), s);
    private static Formula Section() => Call("inter", Base(), F.Id("S"));
    private static Formula PureSection() => Call("inter", Pure(), F.Id("S"));
    private static Formula Hypotheses() => And(Call("IsClosed", F.Id("C")),
        All("x", F.Id("V"), Implies(And(
            new Formula.Relation(F.Id("x"), FormulaRelationOperator.MemberOf, F.Id("C")),
            new Formula.Relation(F.Id("x"), FormulaRelationOperator.NotEqual, D(0))),
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Call("u", F.Id("x"))))));
    private static Formula Telescope(Formula body) => All("V", F.Id("Type"),
        Seq(OpenBracket, Call("NormedAddCommGroup", F.Id("V")), CloseBracket, Sp,
            OpenBracket, Call("NormedSpace", Real(), F.Id("V")), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", Real(), F.Id("V")), CloseBracket, Sp,
            All("C", Call("PointedCone", Real(), F.Id("V")),
                All("u", Call("LinearMap", Real(), F.Id("V"), Real()), body))));
}
