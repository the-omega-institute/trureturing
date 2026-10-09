using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrossPolytopeFaceCountsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/CrossPolytopeFaceCounts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/dai2026crosspolytopes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative weighted sums of coordinate cross polytopes have a signed acyclic formula for every face dimension.",
        H("Faces of Minkowski sums of cross polytopes"),
        Blocks(
            Paragraph(Text("Let n and m be arbitrary natural numbers. Coordinates are indexed by Fin n and summands by Fin m. Each support I(i) is a nonempty finite set of coordinates and each weight w(i) is a nonnegative real number. Equation (3) of Dai, Hou, Liu, Thawinrak and Wang defines the corresponding Minkowski sum. Problem 5.4 asks for its f-vector and, in the simple case, its ordinary h-vector. The formula below supplies the nonempty face counts for this whole family, with real weights in place of integer weights.")),
            Node("cross-polytope-ambient", "Real coordinate space", "Ambient",
                "Ambient(n) is the real vector space Fin n to R, including the zero-dimensional space when n is zero."),
            Node("cross-polytope-data", "Unsigned data", "RawData",
                "RawData(n,m) consists of a finite set J of summand indices and a function S assigning a finite coordinate set S(i) to every summand index. No validity or realizability condition is built into this type."),
            Node("cross-polytope-hull", "Coordinate cross polytope", "crossHull",
                "For every finite coordinate set I, crossHull(I) is the real convex hull of all e(j) and -e(j) with j in I. Here e(j) is the coordinate vector with entry one at j and zero elsewhere. An empty I gives the empty convex hull; the theorem requires each summand support to be nonempty.",
                AssessedProvenance.FromLiterature(Source)),
            Node("cross-polytope-sum", "Actual Minkowski sum", "actualQ",
                "For arbitrary supports and real weights, actualQ(I,w) is the sum over all i in Fin m of w(i) times crossHull(I(i)), using set addition and scalar multiplication. The empty sum is the singleton containing zero. A zero weight on a nonempty summand also gives that singleton. This is the actual convex set whose faces are counted.",
                AssessedProvenance.FromLiterature(Source)),
            Node("cross-polytope-active", "Positive-weight summands", "active",
                "For every real weight function w, active(w) is A = {i : w(i) > 0}. In the theorem all other weights are zero, so they contribute no directions or face choices."),
            Node("cross-polytope-support", "Union of coordinate supports", "support",
                "For any set A of summand indices, support(I,A) is the union of I(i) over i in A. In the counting formula U = support(I,active(w)) and d is the cardinality of U."),
            Node("cross-polytope-zero", "Zero coordinates", "zeroSet",
                "For q = (J,S), zeroSet(I,q) is Z = support(I,J). Every support in J will have zero support value under a realizing normal, and all coordinates of Z vanish under that normal."),
            Node("cross-polytope-remaining", "Remaining summands", "remaining",
                "For A and q = (J,S), remaining(A,q) is A minus J. It contains exactly the positive-weight summands with positive support value in feasible data."),
            Node("cross-polytope-vertices", "All remaining coordinates", "vertexSet",
                "For I, A and q, vertexSet(I,A,q) is V = support(I,A) minus zeroSet(I,q). Every coordinate of V is retained, whether or not it occurs in a selected set S(i)."),
            Node("cross-polytope-selected", "Coordinates carrying signs", "selected",
                "For A and q, selected(A,q) is T, the union of S(i) over i in remaining(A,q). A sign is chosen once per coordinate of T and is shared by every summand using that coordinate."),
            Node("cross-polytope-vertex-type", "The full vertex type", "Vertex",
                "Vertex(I,A,q) is the subtype of Fin n consisting of the members of V. Its elements include unselected coordinates and isolated vertices."),
            Node("cross-polytope-equality", "Equality graph", "equalityGraph",
                "On Vertex(I,A,q), two distinct vertices are adjacent exactly when there is an i in remaining(A,q) for which both coordinates belong to S(i). The graph is undirected and has no graph loops."),
            Node("cross-polytope-components", "Equality components", "Component",
                "Component(I,A,q) is the set of connected components of the equality graph. Its cardinality c counts every isolated vertex, including those outside T. When V is empty, c is zero."),
            Node("cross-polytope-strict", "Strict relation on components", "strictRel",
                "For components C and D, strictRel(I,A,q,C,D) holds exactly when some remaining summand i has coordinates a and b in V with a in I(i) but outside S(i), b in S(i), and components C and D respectively. Thus the absolute value at a must be smaller than that at b. This relation may have a self-loop even though the equality graph does not."),
            Node("cross-polytope-valid", "Valid unsigned choices", "validChoice",
                "validChoice(I,A,q) requires J to be a subset of A; S(i) to be empty for every i outside A minus J; and, for each i in A minus J, S(i) to be nonempty and a subset of I(i) minus Z. The empty selections outside the remaining indices make the data representation unique."),
            Node("cross-polytope-feasible", "Acyclic choices", "feasible",
                "feasible(I,A,q) is validChoice together with the requirement that no component C is related to itself by a nonempty finite path of strictRel. In particular, a single strict self-loop is a forbidden cycle. Acyclicity refers to this strict relation on components, rather than to the undirected equality graph."),
            Node("cross-polytope-geometric-count", "Faces counted by actual dimension", "geometricFaceCount",
                "For arbitrary I, w and natural r, geometricFaceCount(I,w,r) is the natural cardinality of the sets F in Ambient(n) satisfying all three conditions: F is nonempty; F is an exposed subset of actualQ(I,w); and the real finrank of the direction of the affine span of F is r. The zero functional exposes the whole polytope, so it is included. The empty face is excluded and can be assigned its usual separate count one."),
            Describe.Lean(
                DescribeId.Create("cross-polytope-combinatorial-sum"),
                DeclarationHandle.Create(Prefix + "combinatorialSum"),
                H("The finite signed sum"),
                StatementSource.FromAuthor(SumFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The sum ranges over every q in RawData(n,m). In this formula A = active(w), U = support(I,A), c(q) is the cardinality of Component(I,A,q), and T(q) = selected(A,q). The term is 2 raised to the cardinality of T(q) precisely when q is feasible and d minus c(q) equals r, and is zero otherwise. Subtraction is natural-number subtraction. Each factor two counts the two signs of one selected coordinate. No geometric face or existential normal occurs in the summation criterion."))),
                DescribeRole.Definition),
            Node("cross-polytope-chosen-hull", "Signed component hulls", "chosenHull",
                "For supports I, data q, any real sign function s on Fin n and a summand i, chosenHull(I,q,s,i) equals crossHull(I(i)) if i is in J. Otherwise it is the convex hull of s(j) times e(j) for j in S(i). Realizing faces require s(j) to be either one or minus one only on T; values outside T are irrelevant."),
            Node("cross-polytope-signed-face", "The signed Minkowski face", "signedFace",
                "For I, w, q and s, signedFace(I,w,q,s) is the sum over i in active(w) of w(i) times chosenHull(I,q,s,i). It is a set in the same ambient space as actualQ. For feasible q and signs in {1,-1} on T, the proof produces one common linear functional exposing exactly these component hulls and their actual weighted sum."),
            Describe.Lean(
                DescribeId.Create("full-cross-polytope-face-count"),
                DeclarationHandle.Create(Prefix + "full_cross_polytope_face_count"),
                H("Complete face-count formula"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every n and m, every support function I with nonempty I(i), every nonnegative real weight function w, and every natural r at most the cardinality of support(I,active(w)), the actual geometric face count equals the finite signed acyclic-data sum. There is no requirement that weights be strictly positive or distinct, supports be distinct, the incidence graph be connected, or the sum be full-dimensional. Zero-dimensional ambient spaces and empty active sets remain in scope.")),
                    Paragraph(Text("A linear functional selects, in each positive-weight summand, either its whole cross polytope at zero support value or the signed coordinate vertices at its positive maximum absolute value. Equal maxima give the equality graph; strictly smaller coordinates give the strict component relation. Conversely, a linear extension of acyclic reachability assigns strictly increasing positive heights to components, and global coordinate signs turn these heights into one common exposing functional. Positivity of the active weights makes equality of the resulting sum faces recover every component face, hence the zero block, selected sets and signs on T.")),
                    Paragraph(Text("The direction of the actual affine span has an annihilator consisting of functionals zero on Z whose signed coefficients agree along each equality edge. Its dimension is n minus d plus c: the coordinates outside U are free, and the remaining coefficients form the kernel of the equality graph's real Laplacian. The dual dimension identity gives face dimension d minus c. The resulting dimension-preserving correspondence has exactly 2 raised to the cardinality of T sign choices above each feasible unsigned datum, yielding the sum.")),
                    Paragraph(Text("When no weight is positive, the only feasible datum has empty J, empty selections, no vertices and no components; both sides count the unique point face in dimension zero. The datum J = A gives the whole polytope. The usual f-vector adds the empty-face entry one. For a relatively d-dimensional simple polytope, its ordinary h-polynomial follows from the standard transform h(z) = sum over r of f(r) z raised to d-r times (1-z) raised to r. This is the ordinary simple-polytope h-vector, not the Ehrhart h-star polynomial. No simplicity criterion or formula for arbitrary type B generalized permutohedra is asserted."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder"))]));

    private static DocumentBlock Node(string id, string title, string name, string prose,
        AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), FormulaLogicOperator.And, Seq(Open, right, Close));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula Fin(string name) => Call("Fin", F.Id(name));
    private static Formula Telescope(Formula body) =>
        All("n", Nat(), All("m", Nat(),
            All("I", Arrow(Fin("m"), Call("Finset", Fin("n"))),
                All("w", Arrow(Fin("m"), Real()), All("r", Nat(), body)))));

    private static Formula SumFormula()
    {
        Formula I = F.Id("I"), w = F.Id("w"), r = F.Id("r"), q = F.Id("q");
        Formula A = Call("active", w), U = Call("support", I, A);
        Formula dimension = new Formula.Binary(Call("card", U), FormulaBinaryOperator.Subtract,
            Call("NatCard", Call("Component", I, A, q)));
        Formula condition = And(Call("feasible", I, A, q), Equal(dimension, r));
        Formula signs = new Formula.Power(D(2),
            Call("card", Call("selected", A, q)));
        Formula sum = Seq(Sum, Underscore,
            Grp(Seq(q, Sp, InMacro, Sp, Call("RawData", F.Id("n"), F.Id("m")))), Sp,
            Call("ite", condition, signs, D(0)));
        return Disp(Telescope(Equal(Call("combinatorialSum", I, w, r), sum)));
    }

    private static Formula TheoremFormula()
    {
        Formula I = F.Id("I"), w = F.Id("w"), r = F.Id("r"), i = F.Id("i");
        Formula nonempty = All("i", Fin("m"), Call("Nonempty", Call("I", i)));
        Formula nonnegative = All("i", Fin("m"),
            new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, Call("w", i)));
        Formula bound = new Formula.Relation(r, FormulaRelationOperator.LessThanOrEqual,
            Call("card", Call("support", I, Call("active", w))));
        return Disp(Telescope(Imp(nonempty, Imp(nonnegative, Imp(bound,
            Equal(Call("geometricFaceCount", I, w, r), Call("combinatorialSum", I, w, r)))))));
    }
}
