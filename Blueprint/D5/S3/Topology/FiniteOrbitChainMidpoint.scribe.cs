using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteOrbitChainMidpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original finite-cost gluing chains admit prescribed-cost cuts, and compact original chain quotients have exact midpoints at finite distance.",
        H("Cuts and midpoints in original chain quotients"),
        Blocks(
            Paragraph(Text("Let I and J be types in independent universes, X an I-indexed family of extended metric spaces, and A(X) its topological disjoint union. A datum G supplies closed partial isometries indexed by J, with exactly the original generating relation Step(G), equivalence closure Rel(G), finite chains Chain(G,a,b,c) and chain distance delta(G,a,b). A paid move adds the extended distance inside one piece; a forward or inverse gluing move adds zero. All these notions are those of FiniteOrbitChainMetric.")),
            Paragraph(Text("Write Split(X) for the following property, with no compactness or finiteness assumption: for every i, x,y in X(i), and s in ENNReal, if edist(x,y) is finite and s is at most edist(x,y), there exists z in X(i) with edist(x,z) at most s and edist(z,y) at most edist(x,y)-s. ENNReal denotes the nonnegative reals together with infinity. A geodesic piece satisfies this property, but the property itself is the hypothesis used below.")),
            Describe.Lean(DescribeId.Create("original-chain-prescribed-cost-cut"),
                Handle("original_chain_cut"), H("A cut at any finite cumulative cost"),
                StatementSource.FromAuthor(F.Disp(CutStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Y is any extended metric space and q:A(X) to Y realizes exactly the original chain distance on representatives. No surjectivity of q is required. The result concerns an actual finite-cost original chain, so c is its paid cost rather than its endpoint distance or an attained infimum.")),
                    Paragraph(Text("Induct on the chain. If the prescribed cost s is before the last paid move, keep the point supplied by the prefix and bound the remaining tail by the triangle inequality. Otherwise split that final move at s minus the prefix cost, using Split(X). A zero-cost forward or inverse gluing has equal q-images, so the same cut point works. The empty chain forces s=0. This construction places the cut point in the given target Y throughout.")))),
            Describe.Lean(DescribeId.Create("compact-original-quotient-midpoints"),
                Handle("compact_original_quotient_midpoints"), H("Exact midpoints in the compact original quotient"),
                StatementSource.FromAuthor(F.Disp(MidpointStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Here I and J are finite, every X(i) is compact, every full actual Rel(G)-class is finite, and Split(X) holds. Q(G) is the literal Quotient(EqvGen.setoid(Step(G))). Its displayed quotient topology is the original topology of this quotient before the extended metric m is installed. The representative map q(G,a) is the original quotient map. The conclusion supplies one m for the topology equality, chain-distance formula and midpoint assertion simultaneously.")),
                    Paragraph(Text("The finite-orbit chain metric gives m with the original topology, so compactness of the original finite disjoint union descends to this same metric quotient. For each positive epsilon and a pair at finite distance, the chain infimum supplies a chain of finite cost below that distance plus epsilon. Cutting the chain halfway gives a point whose two distances are at most half the endpoint distance plus epsilon. There is no assumption of a minimizing chain or a bound on the number of seam crossings.")),
                    Paragraph(Text("Minimize z to max(edist(a,z),edist(z,b)) over the compact quotient. Extended distances and their maximum are continuous, including at infinity. The approximate midpoint bounds force this minimum to be at most half the finite endpoint distance. The triangle inequality forces both individual distances to equal that half. The construction only needs a point a after a pair a,b has been selected, so it also covers an empty quotient.")))),
            Paragraph(Text("Infinite distances between distinct components are retained. The midpoint assertion only quantifies over pairs with finite distance; it imposes no finite diameter, connectedness or global finite-valued metric. Empty pieces, empty gluing domains, self-gluings, inverse moves and a zero endpoint distance remain included.")),
            Paragraph(Text("The classical complete-midpoint criterion is stated in Bridson and Haefliger, Metric Spaces of Non-Positive Curvature (1999), I.1.4(1); the original disjoint-union chain quotient is described in I.5.18-5.19. The statements here give the prescribed-cost chain cut and exact midpoint stage in the extended metric setting. They do not construct a coherent dyadic family or an isometric real interval, and no novelty claim is made.")),
            Paragraph(Text("For a specified geometric realization one must still identify its original pieces, actual closed partial isometries and full finite equivalence classes with these data, and prove Split(X) for those pieces. The result supplies no identification with a specified marked manifold, no isometric embedding of a whole original piece, and no cone, angle-sum or curvature statement.")))));

    private static Formula CutStatement()
    {
        var a = Id("a"); var b = Id("b"); var c = Id("c"); var s = Id("s"); var z = Id("z");
        var exactDistance = All("a", A, All("b", A,
            Eq(Edist(Call("q", a), Call("q", b)), Delta(a, b))));
        var cut = All("a", A, All("b", A, All("c", Extended,
            Implies(And(Call("Chain", G, a, b, c), Lt(c, F.Infty)),
                All("s", Extended, Implies(Le(s, c), Exists("z", Id("Y"), And(
                    Le(Edist(Call("q", a), z), s),
                    Le(Edist(z, Call("q", b)), Sub(c, s))))))))));
        return Parameters(false, All("Y", Id("Types"),
            F.Seq(F.OpenBracket, Call("EMetricSpace", Id("Y")), F.CloseBracket, F.Sp,
                All("q", new Formula.TypeArrow(A, Id("Y")),
                    Implies(And(exactDistance, Call("Split", Id("X"))), cut)))));
    }

    private static Formula MidpointStatement()
    {
        var a = Id("a"); var b = Id("b"); var z = Id("z"); var m = Id("m");
        var Q = Call("Q", G);
        var finite = All("a", A, Call("Finite", Call("Orbit", G, a)));
        var compact = All("i", Id("I"), Call("CompactSpace", Call("X", Id("i"))));
        var metricDistance = All("a", A, All("b", A,
            Eq(Call("edist", m, Call("q", G, a), Call("q", G, b)), Delta(a, b))));
        var d = Call("edist", m, a, b);
        var midpoints = All("a", Q, All("b", Q, Implies(Lt(d, F.Infty),
            Exists("z", Q, And(
                Eq(Call("edist", m, a, z), Half(d)),
                Eq(Call("edist", m, z, b), Half(d)))))));
        return Parameters(true, Implies(And(compact, finite, Call("Split", Id("X"))),
            Exists("m", Call("EMetricSpace", Q), And(
                Eq(Call("Topology", m), Call("quotientTopology", G)), metricDistance, midpoints))));
    }

    private static Formula Parameters(bool finite, Formula body)
    {
        body = All("G", Call("Datum", Id("I"), Id("J"), Id("X")), body);
        if (finite)
            body = F.Seq(F.OpenBracket, Call("Fintype", Id("I")), F.CloseBracket, F.Sp,
                F.OpenBracket, Call("Fintype", Id("J")), F.CloseBracket, F.Sp, body);
        body = F.Seq(F.OpenBracket,
            All("i", Id("I"), Call("EMetricSpace", Call("X", Id("i")))), F.CloseBracket, F.Sp, body);
        return All("I", Id("Types"), All("J", Id("Types"),
            All("X", new Formula.TypeArrow(Id("I"), Id("Types")), body)));
    }

    private static DeclarationHandle Handle(string selector) =>
        DeclarationHandle.Create("D5/S3/Topology/FiniteOrbitChainMidpoint." + selector);
    private static Formula G => Id("G");
    private static Formula A => Call("A", Id("X"));
    private static Formula Extended => Id("ENNReal");
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Id(s), [.. args]);
    private static Formula All(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), type, body);
    private static Formula Exists(string s, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), type, body);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--) result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => F.Seq(a, F.Sp, F.Lt, F.Sp, b);
    private static Formula Le(Formula a, Formula b) => F.Seq(a, F.Sp, F.Le, F.Sp, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Half(Formula a) => new Formula.Fraction(a, F.D(2));
    private static Formula Edist(Formula a, Formula b) => Call("edist", a, b);
    private static Formula Delta(Formula a, Formula b) => Call("delta", G, a, b);
}
