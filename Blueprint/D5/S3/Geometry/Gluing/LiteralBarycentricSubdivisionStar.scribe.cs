using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class LiteralBarycentricSubdivisionStarDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Geometry/Gluing/LiteralBarycentricSubdivisionStar.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal original second stars equal the union of stars inside complete first parents.",
        H("Literal stars in the second barycentric subdivision"),
        Blocks(
            Paragraph(Text("Let R be the real field and E any real normed vector space, with no finite-dimensional restriction. "
                + "Let p:Fin(4) to E be the original vertex family. Finsets(X) denotes finite subsets of X. "
                + "IsFaceChain(C) means that C is nonempty, every F in C is a nonempty finite subset of Fin(4), "
                + "and every two members of C are comparable by inclusion. "
                + "barycenter(E,p,F) is the sum of p(j) over j in F divided by realCard(F), the cardinality viewed in R. "
                + "For every permutation pi of Fin(4), prefixFace(pi,k) is the image under pi of positions 0 through k. "
                + "Write parentVertices(E,p,pi)(k)=barycenter(E,p,prefixFace(pi,k)). "
                + "For any vertex family q, closedStar(E,q) is the union of convex hulls of face-chain barycenters "
                + "whose actual vertex set contains q(0); openStar(E,q) uses the intrinsic interior of each such hull. "
                + "All nonempty dimensions occur in both unions. Intrinsic interior is taken in each hull's own affine span.")),
            Describe.Lean(DescribeId.Create("second-face-chain"),
                DeclarationHandle.Create(Root + "SecondFaceChain"),
                H("Original chains of original face chains"),
                StatementSource.FromAuthor(F.Disp(SecondChainFormula())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("D is a nonempty finite family "
                    + "of original nonempty face chains C. Inclusion between two C's compares sets "
                    + "of original faces; it does not compare their unions of original vertices. "
                    + "Both levels include every nonempty dimension."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("second-barycenter"),
                DeclarationHandle.Create(Root + "secondBarycenter"),
                H("Average of actual first barycenters"),
                StatementSource.FromAuthor(F.Disp(Context(All("C", Call("Finsets", Call("Finsets", FinFour())),
                    Eq(Call("secondBarycenter", E(), P(), Id("C")),
                        Call("smul", Call("inverse", Call("realCard", Id("C"))),
                            Call("sumFaceBarycenters", E(), P(), Id("C")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("sumFaceBarycenters(E,p,C) "
                    + "sums barycenter(E,p,F) over F in C. Thus the two averaging operations keep "
                    + "their respective cardinalities. This is not the barycenter of the union of C."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("second-hull"), DeclarationHandle.Create(Root + "secondHull"),
                H("Actual second subdivision simplex"),
                StatementSource.FromAuthor(F.Disp(Context(All("D", Id("SecondFaceChain"),
                    Eq(Call("secondHull", E(), P(), Id("D")),
                        Call("convexHull", Id("R"), Call("secondVertices", E(), P(), Id("D")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("secondVertices(E,p,D) is "
                    + "the image of D.chains under secondBarycenter(E,p). All sets lie in the same E."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literal-second-closed-star"),
                DeclarationHandle.Create(Root + "literalClosedStar"),
                H("Literal original closed star"), StatementSource.FromAuthor(F.Disp(LiteralStarDefinition(false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The index condition requires "
                    + "the actual point p(i) in secondVertices(E,p,D). No parent union occurs in this definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literal-second-open-star"),
                DeclarationHandle.Create(Root + "literalOpenStar"),
                H("Literal all-face open star"), StatementSource.FromAuthor(F.Disp(LiteralStarDefinition(true))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The union uses the intrinsic "
                    + "interior of each actual second hull, including the singleton hull at the old vertex."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literal-second-parent-correspondence"),
                DeclarationHandle.Create(Root + "literal_second_closed_and_open_star_iff"),
                H("Literal stars and complete first parents"),
                StatementSource.FromAuthor(F.Disp(LiteralTheoremFormula())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For an affinely independent original family p, a second barycenter "
                        + "equals p(i) precisely when its original face chain is the singleton {{i}}. "
                        + "Expand the nested average in the original affine coordinates. Every inner "
                        + "and outer averaging weight is positive. A face containing j different from i "
                        + "would give a positive j coordinate, contradicting uniqueness of the original "
                        + "affine coefficients. The convex-hull version chooses a positive coefficient "
                        + "in a convex representation and obtains the same singleton chain. Hence "
                        + "p(i) belongs to a second hull precisely when {{i}} belongs to its original D.")),
                    Paragraph(Text("Choose a maximum first chain in D and refine its increasing series "
                        + "with mathlib's LTSeries.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot. "
                        + "The returned embedding retains the original faces. Boolean-lattice covers "
                        + "insert one vertex, so their cardinalities recover a permutation and the four "
                        + "nonempty prefix faces. Retention of {i} forces the first vertex to be i. "
                        + "This is an application of the existing chain-refinement theorem.")),
                    Paragraph(Text("Within a complete parent pi, map S to the chain of prefixFace(pi,k) "
                        + "for k in S. The inverse selects exactly those k whose prefix face lies in C. "
                        + "Distinct prefix cardinalities make this a cardinality-preserving inverse "
                        + "correspondence. Reindexing the actual finite sums identifies each nested "
                        + "barycenter with the existing parent-face barycenter. Both carrier directions "
                        + "preserve the actual vertex set, therefore the hull and its intrinsic interior. "
                        + "For the closed implication the same retained-chain refinement is applied "
                        + "a second time to the parent face chain. Its complete second flag contains "
                        + "every old second vertex, including p(i), and convex-hull monotonicity "
                        + "retains the original closed face. The open implication keeps the original "
                        + "nonmaximal hull exactly; no monotonicity of intrinsic interiors is used.")),
                    Paragraph(Text("The displayed equivalences quantify over all ambient points and "
                        + "all original vertices. They supply the original-carrier bridge to the earlier "
                        + "parent-star characterization. Zero weights, ties and lower-dimensional faces "
                        + "remain inside the definitions. The further radial normalization, "
                        + "coefficient zero-extension identification, deleted-link "
                        + "identification across overlapping parents, and marked retained-quotient "
                        + "identification are distinct propositions; this theorem alone does not assert "
                        + "them or a homeomorphism to a specified manifold."))),
                DescribeRole.Theorem))));

    private static Formula SecondChainFormula()
    {
        var families = Call("Finsets", Call("Finsets", FinFour()));
        var d = Id("D");
        var first = All("C", families, Implies(In(Id("C"), d), Call("IsFaceChain", Id("C"))));
        var nested = All("C", families, All("B", families,
            Implies(And(In(Id("C"), d), In(Id("B"), d)),
                Or(Call("subset", Id("C"), Id("B")), Call("subset", Id("B"), Id("C"))))));
        return All("D", Call("Finsets", families),
            Iff(Call("IsSecondFaceChain", d), And(Call("Nonempty", d), first, nested)));
    }
    private static Formula LiteralStarDefinition(bool open)
    {
        var hull = Call("secondHull", E(), P(), Id("D"));
        var region = open ? Call("intrinsicInterior", Id("R"), hull) : hull;
        var incident = In(Call("p", Id("i")), Call("secondVertices", E(), P(), Id("D")));
        return Context(All("i", FinFour(), All("x", E(),
            Iff(In(Id("x"), Call(open ? "literalOpenStar" : "literalClosedStar", E(), P(), Id("i"))),
                Exists("D", Id("SecondFaceChain"), And(incident, In(Id("x"), region)))))));
    }
    private static Formula LiteralTheoremFormula()
    {
        Formula Correspondence(bool open)
        {
            var parent = Call("parentVertices", E(), P(), Id("pi"));
            var witness = Exists("pi", Call("Perm", FinFour()),
                And(Eq(Call("pi", F.D(0)), Id("i")),
                    In(Id("x"), Call(open ? "openStar" : "closedStar", E(), parent))));
            return Iff(In(Id("x"),
                Call(open ? "literalOpenStar" : "literalClosedStar", E(), P(), Id("i"))), witness);
        }
        return Context(All("i", FinFour(), All("x", E(),
            Implies(Call("AffineIndependent", Id("R"), P()),
                And(Correspondence(false), Correspondence(true))))));
    }

    private static Formula Context(Formula body) => All("E", Id("Types"),
        Implies(Call("RealNormedVectorSpace", E()), All("p", Maps(FinFour(), E()), body)));
    private static Formula Id(string x) => F.Id(x);
    private static Formula E() => Id("E");
    private static Formula P() => Id("p");
    private static Formula FinFour() => Call("Fin", F.D(4));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula Maps(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Exists(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula And(params Formula[] xs) { var r = xs[^1]; for (var k = xs.Length - 2; k >= 0; k--) r = F.Seq(F.Open, xs[k], F.Close, F.Sp, F.Land, F.Sp, F.Open, r, F.Close); return r; }
    private static Formula Or(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Lor, F.Sp, F.Open, b, F.Close);
    private static Formula Implies(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Implies, F.Sp, F.Open, b, F.Close);
    private static Formula Iff(Formula a, Formula b) => F.Seq(F.Open, a, F.Close, F.Sp, F.Iff, F.Sp, F.Open, b, F.Close);
    private static Formula Eq(Formula a, Formula b) => F.Seq(a, F.Sp, F.Eq, F.Sp, b);
    private static Formula In(Formula a, Formula b) => F.Seq(a, F.Sp, F.InMacro, F.Sp, b);
}
