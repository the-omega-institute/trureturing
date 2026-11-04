using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteOrbitChainMetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite actual equivalence classes of closed partial isometries give a chain extended metric with the original quotient topology.",
        H("Finite-orbit chain extended metrics"),
        Blocks(
            Paragraph(Text("Let I and J be types in independent universes and X an I-indexed family of types in a third universe. Each X(i) carries an extended metric, with values in ENNReal, the nonnegative reals together with infinity. Types denotes the appropriate universe of types; maps and dependent families retain these independent universes. Write Y(X) for the topological disjoint union, index(b) and point(b) for the two components of a point, and tag(i,x) for its tagged inclusion. No piece is assumed finite, nonempty, compact, complete or a length space.")),
            Paragraph(Text("A datum G consists of src,dst:J to I, closed subsets dom(j) of X(src(j)) and ran(j) of X(dst(j)), and a bijective isometry iso(j) between these subspaces. Thus ClosedPartialIsometryData(I,J,X) below denotes exactly the dependent record of these five fields together with their closed-domain and closed-range proofs. Empty generators, empty pieces, empty domains and self-identifications are allowed. The relation R is the full equivalence closure of the actual generator relation; finite orbit always means this entire class, including arbitrary finite words and inverses.")),
            Describe.Lean(DescribeId.Create("closed-partial-isometry-datum"),
                Handle("Datum"), H("Closed partial isometry data"),
                StatementSource.FromAuthor(F.Disp(Parameters(false, false,
                    Eq(Call("Datum", Id("I"), Id("J"), Id("X")),
                       Call("ClosedPartialIsometryData", Id("I"), Id("J"), Id("X"))), false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The isometry is between the actual closed subspaces with their induced extended metrics. There is no noncollapse or topology-compatibility field."))), role: DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-generating-step"),
                Handle("Step"), H("The generating relation"),
                StatementSource.FromAuthor(F.Disp(Parameters(false, false,
                    All("a", Y, All("b", Y, Iff(Call("Step", G, Id("a"), Id("b")),
                        Exists("j", Id("J"), Exists("x", Call("dom", G, Id("j")), And(
                            Eq(Id("a"), Call("tag", Call("src", G, Id("j")), Call("val", Id("x")))),
                            Eq(Id("b"), Call("tag", Call("dst", G, Id("j")), Call("val", Call("iso", G, Id("j"), Id("x")))))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("One step uses a supplied generator at a point of its actual domain. Val forgets a subspace membership proof.")))),
            Describe.Lean(DescribeId.Create("full-equivalence-relation"),
                Handle("Rel"), H("The full generated relation"),
                StatementSource.FromAuthor(F.Disp(Parameters(false, false,
                    Eq(Call("Rel", G), Call("EqvGen", Call("Step", G)))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("EqvGen includes reflexivity, symmetry and transitivity without a bound on word length. O(G,a) denotes the set of all b in Y(X) for which Rel(G,a,b).")))),
            Describe.Lean(DescribeId.Create("finite-chains-with-extended-cost"),
                Handle("Chain"), H("Finite chains and extended costs"),
                StatementSource.FromAuthor(F.Disp(Parameters(false, false,
                    All("a", Y, Eq(Call("Chain", G, Id("a")), Call("LeastChainFamily", G, Id("a"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("LeastChainFamily(G,a) is the least predicate on Y(X) times ENNReal closed under four rules: Chain(G,a,a,0); from Chain(G,a,tag(i,x),t), infer Chain(G,a,tag(i,y),t+edist(x,y)); from Chain(G,a,tag(src(j),val(x)),t) for x in dom(j), infer Chain(G,a,tag(dst(j),val(iso(j,x))),t); and from Chain(G,a,tag(dst(j),val(x)),t) for x in ran(j), infer Chain(G,a,tag(src(j),val(inverse(iso(j),x))),t). Every rule ranges over all its well-typed arguments. A finite derivation can have infinite cost."))), role: DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chain-distance-infimum"),
                Handle("distance"), H("The chain distance"),
                StatementSource.FromAuthor(F.Disp(Parameters(false, false,
                    All("a", Y, All("b", Y, Eq(Distance(Id("a"), Id("b")),
                        Call("infimum", Call("chainCosts", G, Id("a"), Id("b"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("ChainCosts(G,a,b) is the set of t in ENNReal satisfying Chain(G,a,b,t). Its infimum is taken in ENNReal; the empty infimum is infinity. In particular, infinity does not mean that there is no finite derivation.")))),
            Describe.Lean(DescribeId.Create("finite-orbit-local-model"),
                Handle("finite_orbit_local_model"), H("Short-chain capture and exact local balls"),
                StatementSource.FromAuthor(F.Disp(LocalStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Only J and the actual orbit at a need be finite here. For each generator, the finitely many orbit centers outside its closed domain have a positive uniform separation from that domain; do the same for its closed range. Take the minimum of these finitely many positive radii and one. If an orbit center lies within this radius of a domain point, it belongs to the domain; the analogous implication holds for the range.")),
                    Paragraph(Text("Induct on the actual chain, tracking an orbit center in the current piece at distance at most the accumulated cost. A paid step uses the triangle inequality. At a generator step the exclusion radius puts the center in the same domain, and the isometry transports both points without changing their distance; inverse steps use the closed range. For the local-ball formula, an infimum strictly below s supplies a chain of cost below s. Conversely a zero-cost relation chain followed by one paid step gives the required upper bound.")))),
            Describe.Lean(DescribeId.Create("original-quotient-chain-metric"),
                Handle("chain_metric_on_original_quotient"), H("An extended metric on the original quotient"),
                StatementSource.FromAuthor(F.Disp(QuotientStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Now both I and J are finite and every actual orbit is finite. Q(G) is Quotient(EqvGen.setoid(Step(G))); q(G,a) is the original quotient map and quotientTopology(G) is the quotient topology of the topological disjoint union before any new metric is installed. Topology(m) and edist(m) are the topology and distance of the displayed extended metric m. The last clause means every piece map is 1-Lipschitz for this same m.")),
                    Paragraph(Text("If the chain distance is zero, short-chain capture puts the endpoint in the closure of its piece's finite orbit fiber. That fiber is closed, so the endpoint already belongs to the original equivalence class. Reverse chains and concatenation give symmetry and the triangle inequality; zero-cost relation chains make the distance invariant under replacing representatives. These facts construct the extended metric on the original quotient, without another zero-distance quotient.")),
                    Paragraph(Text("For an open saturated set V in the original disjoint union and a in V, separate each finite orbit fiber from its piece's closed complement of V. The minimum of these finitely many separation radii and the capture radius is positive. Every smaller chain ball about a lies in V by capture. This proves that every original quotient-open set is metric-open. Conversely the one-step bound makes each piece map 1-Lipschitz, so every metric-open set has open preimage. Thus the topologies agree even for noncompact pieces.")),
                    Paragraph(Text("A finite-cost chain bounds the infimum strictly below infinity, and an infimum strictly below infinity supplies a finite-cost chain. For a two-point piece whose distinct points have infinite distance and no generators, there is still a one-step chain of infinite cost. Identifying those two points by a closed singleton self-gluing instead makes their quotient distance zero. Hence the finite-cost qualifier is necessary and the piece maps need not be isometric embeddings.")))),
            Paragraph(Text("The chain pseudometric construction is classical: Bridson and Haefliger, Metric Spaces of Non-Positive Curvature (1999), I.3 opening and I.5.18-5.19, allow infinity and describe the disjoint union and chain quotient. Their I.5.27-5.28 criterion explicitly assumes a saturated union of representative balls and equality of radial distances at related nearby points. The finite-orbit capture and noncompact topology argument above are deductions proved here, with no claim of novelty or verbatim reproduction of that criterion. Burago, Burago and Ivanov, A Course in Metric Geometry (2001), Definition 3.1.12 and Theorem 3.1.27 describe the chain semimetric; Exercise 3.1.14 gives topology equality under compactness and absence of extra identifications. It does not supply the general noncompact conclusion used here.")),
            Paragraph(Text("Application to a specified geometric realization still requires its actual pieces, closed partial isometries, full finite orbits, and an identification with its original marked quotient. The theorem alone asserts no geodesicity, cell isometric embedding, hyperbolic cone model, angle sum or curvature formula.")))));

    private static Formula LocalStatement()
    {
        var a = Id("a"); var b = Id("b"); var t = Id("t"); var s = Id("s"); var rho = Id("rho");
        var capture = All("b", Y, All("t", Extended, Implies(And(Call("Chain", G, a, b, t), Lt(t, rho)),
            Exists("c", Call("X", Call("index", b)), And(
                Rel(a, Call("tag", Call("index", b), Id("c"))),
                Le(Call("edist", Id("c"), Call("point", b)), t))))));
        var balls = All("b", Y, All("s", Extended, Implies(And(Lt(F.D(0), s), Lt(s, rho)),
            Iff(Lt(Distance(a, b), s), Exists("c", Call("X", Call("index", b)), And(
                Rel(a, Call("tag", Call("index", b), Id("c"))),
                Lt(Call("edist", Id("c"), Call("point", b)), s)))))));
        return Parameters(false, true, All("a", Y, Implies(Call("Finite", Call("O", G, a)),
            Exists("rho", Extended, And(Lt(F.D(0), rho), Lt(rho, Infinity), capture, balls)))));
    }

    private static Formula QuotientStatement()
    {
        var a = Id("a"); var b = Id("b"); var m = Id("m"); var t = Id("t");
        var finite = All("a", Y, Call("Finite", Call("O", G, a)));
        return Parameters(true, true, Implies(finite, Exists("m", Call("EMetricSpace", Call("Q", G)), And(
            Eq(Call("Topology", m), Call("quotientTopology", G)),
            All("a", Y, All("b", Y, Eq(Call("edist", m, Call("q", G, a), Call("q", G, b)), Distance(a, b)))),
            All("a", Y, All("b", Y, Iff(Eq(Distance(a, b), F.D(0)), Rel(a, b)))),
            All("a", Y, All("b", Y, Iff(Eq(Distance(a, b), Infinity),
                Neg(Exists("t", Extended, And(Call("Chain", G, a, b, t), Lt(t, Infinity))))))),
            All("i", Id("I"), All("x", Call("X", Id("i")), All("y", Call("X", Id("i")),
                Le(Call("edist", m, Call("q", G, Call("tag", Id("i"), Id("x"))),
                    Call("q", G, Call("tag", Id("i"), Id("y")))), Call("edist", Id("x"), Id("y"))))))))));
    }

    private static Formula Parameters(bool finiteI, bool finiteJ, Formula body, bool datum = true)
    {
        if (datum) body = All("G", Call("Datum", Id("I"), Id("J"), Id("X")), body);
        var hypotheses = new System.Collections.Generic.List<Formula> {
            All("i", Id("I"), Call("EMetricSpace", Call("X", Id("i")))) };
        if (finiteI) hypotheses.Add(Call("Fintype", Id("I")));
        if (finiteJ) hypotheses.Add(Call("Fintype", Id("J")));
        for (var i = hypotheses.Count - 1; i >= 0; i--)
            body = F.Seq(F.OpenBracket, hypotheses[i], F.CloseBracket, F.Sp, body);
        return All("I", Id("Types"), All("J", Id("Types"),
            All("X", new Formula.TypeArrow(Id("I"), Id("Types")), body)));
    }
    private static DeclarationHandle Handle(string selector) =>
        DeclarationHandle.Create("D5/S3/Topology/FiniteOrbitChainMetric." + selector);
    private static Formula G => Id("G");
    private static Formula Y => Call("Y", Id("X"));
    private static Formula Extended => Id("ENNReal");
    private static Formula Infinity => F.Infty;
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
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Neg(Formula p) => F.Seq(F.Neg, F.Sp, F.Open, p, F.Close);
    private static Formula Distance(Formula a, Formula b) => Call("distance", G, a, b);
    private static Formula Rel(Formula a, Formula b) => Call("Rel", G, a, b);
}
