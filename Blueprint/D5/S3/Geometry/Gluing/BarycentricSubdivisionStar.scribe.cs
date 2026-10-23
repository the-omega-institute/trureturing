using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class BarycentricSubdivisionStarDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/Geometry/Gluing/BarycentricSubdivisionStar.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual face-chain stars are characterized by weak and strict parent coordinate maxima.",
        H("Stars in the geometric barycentric subdivision of a tetrahedron"),
        Blocks(
            Paragraph(Text("Let R denote the real field, and let E be any real normed vector space. "
                + "The ambient space need not have finite dimension. Fix an affinely independent "
                + "family p indexed by Fin(4). Its parent simplex is the convex hull of its four vertices. "
                + "A parent face is a nonempty finite subset of Fin(4). A face chain is a nonempty finite "
                + "collection of parent faces, any two of which are comparable by inclusion. "
                + "Every chain dimension is allowed, including singleton chains.")),
            Describe.Lean(DescribeId.Create("face-chain"), DeclarationHandle.Create(Root + "FaceChain"),
                H("Chains of actual parent faces"), StatementSource.FromAuthor(F.Disp(ChainFormula())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("FaceChain is the type of collections C "
                    + "satisfying the displayed conditions, together with proofs of those conditions. "
                    + "Finsets(X) denotes finite subsets of X. Nonempty means existence of an element; "
                    + "subset is ordinary inclusion. The faces projection forgets the proofs."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("face-barycenter"), DeclarationHandle.Create(Root + "barycenter"),
                H("Geometric face barycenters"), StatementSource.FromAuthor(F.Disp(Context(
                    All("F", Call("Finsets", FinFour()), Eq(Call("barycenter", E(), P(), Id("F")),
                        Call("smul", Call("inverse", Call("realCard", Id("F"))), Call("faceSum", E(), P(), Id("F")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("realCard(F) is the cardinality viewed in R, "
                    + "faceSum(E,p,F) is the sum of p(i) over i in F, and smul is scalar multiplication. "
                    + "The formula defines the barycenter for every finite F; only nonempty F occur in chains."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chain-hull"), DeclarationHandle.Create(Root + "chainHull"),
                H("The actual chain simplex"), StatementSource.FromAuthor(F.Disp(Context(
                    All("C", Id("FaceChain"), Eq(Call("chainHull", E(), P(), Id("C")),
                        Call("convexHull", Id("R"), Call("vertices", E(), P(), Id("C")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("vertices(E,p,C) is exactly the image "
                    + "of C.faces under F mapped to barycenter(E,p,F). Thus chainHull is the convex hull "
                    + "of actual geometric barycenters, independently of any coordinate comparison."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("closed-star"), DeclarationHandle.Create(Root + "closedStar"),
                H("Union of all incident closed chain simplices"), StatementSource.FromAuthor(F.Disp(StarDefinition(false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Incidence is geometric: p(0) must "
                    + "belong to the barycenter vertex set of the chain. Affine independence forces "
                    + "a face whose barycenter is p(0) to be the singleton face containing 0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("open-star"), DeclarationHandle.Create(Root + "openStar"),
                H("Union of all incident intrinsic interiors"), StatementSource.FromAuthor(F.Disp(StarDefinition(true))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("intrinsicInterior(R,Q) is the interior "
                    + "computed in Q's own affine span and then included in E. The union ranges over "
                    + "all incident chains, including lower-dimensional faces and the singleton at p(0). "
                    + "It is not restricted to interiors of maximal subdivision simplices."))), DescribeRole.Definition),
            Paragraph(Text("For beta:Fin(4) to R, sum(beta) is the sum of its four entries, and "
                + "pointSum(E,p,beta) is the sum of beta(i) times p(i). Nonnegative entries with sum one "
                + "ensure this point lies in the parent convex hull. The displayed theorem imposes no "
                + "further assumption on the point. Ties and zero coefficients are retained. "
                + "The star characterization is the vertex case of Lemma 2.6, pages 56–57, in the cited source. "
                + "Here the closed star is expressed directly as the finite union of incident closed simplices.")),
            Describe.Lean(DescribeId.Create("actual-closed-and-open-star"),
                DeclarationHandle.Create(Root + "actual_closed_and_open_star_iff"),
                H("Weak maximum for the closed star; strict maximum for the all-face open star"),
                StatementSource.FromAuthor(F.Disp(TheoremFormula())),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Geometry/delfsknebusch1984separation")),
                Blocks(
                    Paragraph(Text("For an arbitrary incident chain, the barycenter incidence condition "
                        + "forces its singleton face {0}, and comparability forces every other face to "
                        + "contain 0. Each barycenter therefore has coordinate 0 at least as large as "
                        + "every other coordinate. Convex combinations and uniqueness of parent affine "
                        + "coefficients establish the closed-star implication.")),
                    Paragraph(Text("Conversely, sort the parent coefficients in decreasing order, breaking "
                        + "ties by the original index. A maximum at 0 makes 0 first. The actual prefix "
                        + "face barycenters receive weights beta(pi(0))-beta(pi(1)), twice the difference "
                        + "beta(pi(1))-beta(pi(2)), three times the difference beta(pi(2))-beta(pi(3)), and four times "
                        + "beta(pi(3)). These nonnegative weights sum to one and reconstruct every parent "
                        + "coordinate by a triangular identity. The same triangular transformation "
                        + "proves affine independence of the prefix barycenters.")),
                    Paragraph(Text("Under strict dominance the first weight is positive. Keep precisely "
                        + "the positive weights and their prefix faces. This is an actual face chain "
                        + "still incident to p(0). In the direction space of its affine span the "
                        + "barycenters form an affine basis. The affine-basis interior theorem and "
                        + "affine-isometry transport place their positive combination in the intrinsic "
                        + "interior. This argument includes a zero-dimensional affine span.")),
                    Paragraph(Text("For necessity in the open star, a relative-interior point admits a "
                        + "short extension away from p(0) that remains in its chain hull. If any other "
                        + "parent coordinate were tied with coordinate 0, this extension would make "
                        + "that coordinate larger than coordinate 0, contradicting the closed-star "
                        + "implication. Thus all three comparisons are strict."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-prefix-face"),
                DeclarationHandle.Create(Root + "prefixFace"),
                H("Complete original parent flags"),
                StatementSource.FromAuthor(F.Disp(All("pi", Call("Perm", FinFour()),
                    All("k", FinFour(), Eq(Call("prefixFace", Id("pi"), Id("k")),
                        Call("image", Id("pi"), Call("Iic", Id("k")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Iic(k) consists of positions "
                    + "from 0 through k. Its image under pi is an original face with k+1 vertices. "
                    + "Write parentVertices(E,p,pi)(k)=barycenter(E,p,prefixFace(pi,k)). "
                    + "These are actual first-level barycenters in E; in particular the zeroth is p(pi(0))."))),
                DescribeRole.Definition))));

    private static Formula ChainFormula()
    {
        var faces = Call("Finsets", FinFour());
        var c = Id("C");
        var f = Id("F");
        var g = Id("G");
        var nonemptyFaces = All("F", faces, Implies(In(f, c), Call("Nonempty", f)));
        var comparable = All("F", faces, All("G", faces,
            Implies(And(In(f, c), In(g, c)), Or(Call("subset", f, g), Call("subset", g, f)))));
        return All("C", Call("Finsets", faces),
            Iff(Call("IsFaceChain", c), And(Call("Nonempty", c), nonemptyFaces, comparable)));
    }
    private static Formula Context(Formula body) => All("E", Id("Types"),
        Implies(Call("RealNormedVectorSpace", E()), All("p", Maps(FinFour(), E()), body)));
    private static Formula StarDefinition(bool open)
    {
        var hull = Call("chainHull", E(), P(), Id("C"));
        var region = open ? Call("intrinsicInterior", Id("R"), hull) : hull;
        var incident = In(Call("p", F.D(0)), Call("vertices", E(), P(), Id("C")));
        var witness = Exists("C", Id("FaceChain"), And(incident, In(Id("x"), region)));
        return Context(All("x", E(), Iff(
            In(Id("x"), Call(open ? "openStar" : "closedStar", E(), P())), witness)));
    }
    private static Formula TheoremFormula()
    {
        var hypotheses = And(Call("AffineIndependent", Id("R"), P()),
            All("j", FinFour(), Le(F.D(0), Call("beta", Id("j")))),
            Eq(Call("sum", Id("beta")), F.D(1)),
            Eq(Id("x"), Call("pointSum", E(), P(), Id("beta"))));
        var conclusions = And(
            Iff(In(Id("x"), Call("closedStar", E(), P())), Comparisons(false)),
            Iff(In(Id("x"), Call("openStar", E(), P())), Comparisons(true)));
        return Context(All("beta", Maps(FinFour(), Id("R")),
            All("x", E(), Implies(hypotheses, conclusions))));
    }
    private static Formula Comparisons(bool strict) => All("j", FinFour(), Implies(Ne(Id("j"), F.D(0)),
        strict ? Lt(Call("beta", Id("j")), Call("beta", F.D(0))) : Le(Call("beta", Id("j")), Call("beta", F.D(0)))));
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
    private static Formula Ne(Formula a, Formula b) => F.Seq(a, F.Sp, F.Neq, F.Sp, b);
    private static Formula In(Formula a, Formula b) => F.Seq(a, F.Sp, F.InMacro, F.Sp, b);
    private static Formula Le(Formula a, Formula b) => F.Seq(a, F.Sp, F.Le, F.Sp, b);
    private static Formula Lt(Formula a, Formula b) => F.Seq(a, F.Sp, F.Lt, F.Sp, b);
}
