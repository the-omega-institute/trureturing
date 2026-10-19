using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class KovacecStrengthenedMarcusDeOliveiraRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/kovacec2026strongermoc");
    private const string Conjecture = "Given any two n-multisets of complex numbers A, B such that a Jordan curve J and the bounded component J(A, B) are defined, there holds ∆(A, B) ⊆ closure(J(A, B)).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant of a rational orthogonal conjugate escapes the bounded region enclosed by the exterior boundary of a three-dimensional sigma-point graph.",
        H("Kovačec's strengthened Marcus–de Oliveira conjecture is false"),
        Blocks(
            Node("sigmaPoint", "Permutation products", SigmaFormula(),
                "Section 1, p. 2: \"Often one writes z_σ = z_σ(A, B) = ∏ᵢ₌₁ⁿ (aᵢ + b_{σ(i)}), and calls these points σ-points.\" Functions a and b on Fin n represent the two multisets, retaining multiplicity. The product runs over all zero-based indices i in Fin n; sigma is a permutation of these indices.", AssessedProvenance.FromLiterature(Source)),
            Node("detRange", "Determinants of unitary conjugates", RangeFormula(),
                "Section 1, p. 2: \"Putting ∆ = ∆(A, B) = {det(D_A + U D_B U*) : U ∈ U(n)}, we can say this also this way: Conjecture 1’’. For any n-multisets of complex numbers A, B we have ∆(A, B) ⊆ C(A, B).\" Matrix.diagonal forms the two diagonal matrices, and star on a complex matrix is its conjugate transpose. Membership in Matrix.unitaryGroup supplies the unitary condition.", AssessedProvenance.FromLiterature(Source)),
            Node("graph", "The transposition-segment graph", GraphFormula(),
                "Section 2, p. 4, joins permutations \"that differ by exactly one transposition\". Definitions 6a, p. 4: \"A metric (linear) graph G = G(V, E) is a subset of the plane consisting of a family V of complex numbers (or pairs of reals) as vertices and a family E of segments [v, w] with v, w ∈ V as edges.\" Here the vertices are the sigma-points and the edges are the real closed segments joining sigma and sigma * Equiv.swap i j, for i ≠ j. The repeated orientation of an edge does not change its union.", AssessedProvenance.FromLiterature(Source)),
            Node("exterior", "Points with arbitrarily long unobstructed segments", ExteriorFormula(),
                "Definitions 6b, p. 5: \"A point p is an exterior point of a finite metric linear graph G if for all M > 0 there is a point q at distance M from p such that [p, q] does not intersect any edge of G. The set of all exterior points is the exterior of G.\" Disjointness from the union G is exactly disjointness from every edge. The length M is a positive real number and the endpoint q is complex.", AssessedProvenance.FromLiterature(Source)),
            Node("IsJordanCurve", "Simple closed curves", JordanFormula(),
                "Page 5: \"the exterior of such a graph is certainly connected and typically will have a boundary which is a Jordan-curve J.\" A Jordan curve is represented as the range of a continuous injective map gamma from Circle to the complex plane. Circle is the unit circle, and equality of ranges specifies the whole curve.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The strengthened conjecture", Disp(Iff(X("claim"), ClaimBody())),
                "Conjecture 7 (strengthened MOC), p. 5: \"" + Conjecture + "\" The frontier of exterior(graph a b) is J. For each x outside J whose connected component in Jᶜ is bounded, the assertion includes detRange a b in the closure of that component. This formulation quantifies over every bounded component and does not assume a Jordan curve theorem. The finite indexing includes multiplicities and all natural dimensions.", AssessedProvenance.FromLiterature(Source)),
            Node("result", "An escaping determinant at dimension three", Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "Take a=(−3−i,−5−2i,4−3i), b=(−2+i,4+3i,−2−5i), and Q=(1/7)[[−3,−2,6],[−2,−6,−3],[−6,3,−2]]. The real orthogonal Q is unitary and gives determinant (2864+1840i)/49. The exterior is the complement of the x-monotone hexagon with vertices −130+10i, 232+376i, 280+280i, (7672+4424i)/155, 24−20i and −28−56i. Its frontier is parametrized continuously and injectively by Circle. The component containing zero is bounded and its closure is contained in the hexagon. The determinant lies below its lower boundary, since 12 Re d−280−11 Im d=408/49>0. Thus the stated inclusion fails. The original convex-hull Marcus–de Oliveira conjecture is a separate assertion.", AssessedProvenance.FromRepo(Source), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kovacec-2026-strengthened-marcus-de-oliveira"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("kov-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(X("N")));
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula C => Seq(Mathbb, Grp(X("C")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Vectors => Seq(Fin(X("n")), Sp, To, Sp, C);
    private static Formula Matrices => Call("Matrix", Fin(X("n")), Fin(X("n")), C);
    private static Formula Permutations => App(Qualified("Equiv", "Perm"), Fin(X("n")));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp,
        Parenthesized(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp,
        Parenthesized(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Negate(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula WithVectors(Formula body) => All("n", N, All("a", Vectors, All("b", Vectors, body)));
    private static Formula PredicateSet(string name, Formula type, Formula predicate) => Seq(OpenBrace,
        X(name), Colon, Sp, type, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Boundary() => Call("frontier", Call("exterior", Call("graph", X("a"), X("b"))));
    private static Formula Component() => Call("connectedComponentIn", new Formula.Power(Parenthesized(Boundary()), X("c")), X("x"));

    private static Formula SigmaFormula()
    {
        var term = Add(App(X("a"), X("i")), App(X("b"), App(X("sigma"), X("i"))));
        var product = Seq(new Formula.Subscript(Prod, Seq(X("i"), Colon, Sp, Fin(X("n")))), Sp, Parenthesized(term));
        return Disp(WithVectors(All("sigma", Permutations,
            Eq(Call("sigmaPoint", X("a"), X("b"), X("sigma")), product))));
    }

    private static Formula RangeFormula()
    {
        var product = new Formula.Binary(new Formula.Binary(X("U"), FormulaBinaryOperator.Multiply,
            App(Qualified("Matrix", "diagonal"), X("b"))), FormulaBinaryOperator.Multiply, Call("star", X("U")));
        var determinant = App(Qualified("Matrix", "det"), Parenthesized(Add(
            App(Qualified("Matrix", "diagonal"), X("a")), product)));
        var body = Some("U", Matrices, And(Member(X("U"), App(Qualified("Matrix", "unitaryGroup"), Fin(X("n")), C)),
            Eq(X("z"), determinant)));
        return Disp(WithVectors(Eq(Call("detRange", X("a"), X("b")), PredicateSet("z", C, body))));
    }

    private static Formula GraphFormula()
    {
        var transposed = new Formula.Binary(X("sigma"), FormulaBinaryOperator.Multiply,
            App(Qualified("Equiv", "swap"), X("i"), X("j")));
        var edge = Call("segment", R, Call("sigmaPoint", X("a"), X("b"), X("sigma")),
            Call("sigmaPoint", X("a"), X("b"), transposed));
        Formula Union(string name, Formula type, Formula body) => Seq(new Formula.Subscript(
            Cup, Seq(X(name), Colon, Sp, type)), Sp, body);
        var neq = new Formula.Relation(X("i"), FormulaRelationOperator.NotEqual, X("j"));
        var allEdges = Union("sigma", Permutations, Union("i", Fin(X("n")), Union("j", Fin(X("n")),
            Seq(new Formula.Subscript(Cup, neq), Sp, edge))));
        return Disp(WithVectors(Eq(Call("graph", X("a"), X("b")), allEdges)));
    }

    private static Formula ExteriorFormula()
    {
        var longSegment = Some("q", C, And(Eq(Call("dist", X("p"), X("q")), X("M")),
            Call("Disjoint", Call("segment", R, X("p"), X("q")), X("G"))));
        var body = All("M", R, Imp(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, X("M")), longSegment));
        return Disp(All("G", Call("Set", C), Eq(Call("exterior", X("G")), PredicateSet("p", C, body))));
    }

    private static Formula JordanFormula()
    {
        var body = Some("gamma", Seq(X("Circle"), Sp, To, Sp, C),
            And(Call("Continuous", X("gamma")), And(App(Qualified("Function", "Injective"), X("gamma")),
                Eq(App(Qualified("Set", "range"), X("gamma")), X("J")))));
        return Disp(All("J", Call("Set", C), Iff(Call("IsJordanCurve", X("J")), body)));
    }

    private static Formula ClaimBody()
    {
        var inclusion = new Formula.Relation(Call("detRange", X("a"), X("b")), FormulaRelationOperator.SubsetOf,
            Call("closure", Component()));
        return WithVectors(Imp(Call("IsJordanCurve", Boundary()), All("x", C,
            Imp(Negate(Member(X("x"), Boundary())), Imp(App(Qualified("Bornology", "IsBounded"), Component()), inclusion)))));
    }
}
