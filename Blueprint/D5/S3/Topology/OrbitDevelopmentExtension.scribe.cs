using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class OrbitDevelopmentExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local isometries compatible on the original generator faces extend across a saturated union of balls around one finite complete orbit.",
        H("Extending compatible developments around an original orbit"),
        Blocks(
            Paragraph(Text("Let I and J be types, X an I-indexed family of extended metric spaces, and A(X) the original disjoint union Sigma X. The four universes of I, J, the fibers X(i), and the target Y are independent. G is a FiniteOrbitChainMetric.Datum: it specifies src(j), dst(j), closed original domains dom(j), closed original ranges ran(j), and bijective isometries iso(j) between these subspaces. Point(i,x) is the original tagged point. Rel(G,b,c) is the full equivalence closure of its actual generator steps, and Orbit(G,a) is the set of b satisfying Rel(G,a,b). All source distances below are the given extended distances of X(i).")),
            Describe.Lean(DescribeId.Create("actual-orbit-source-centers"), Handle("Center"),
                H("Centers in one source fiber"),
                StatementSource.FromAuthor(F.Disp(CenterStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Center(G,a,i) is precisely the subtype of c in X(i) for which Rel(G,a,Point(i,c)). Its value val(c) is an original source point. Distinct proofs of the same membership do not create distinct centers. Any separate labels for the same tagged point must describe this same subtype element; no independent placement values are assigned to repeated descriptions."))), role: DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("union-of-source-orbit-balls"), Handle("Nearby"),
                H("The union of orbit balls"),
                StatementSource.FromAuthor(F.Disp(Base(All("t", Id("ENNReal"), All("b", A,
                    Iff(Call("Nearby", G, a, Id("t"), Id("b")),
                        Exists("c", Centers(Call("first", Id("b"))),
                            Lt(Call("edist", Call("val", Id("c")), Call("second", Id("b"))), Id("t"))))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Nearby(G,a,t,b) means that some actual orbit center in the same source as b is within extended distance t of b. Thus each fiber of this set is a union of its original open balls. This definition uses neither a distance on A(X) nor a quotient distance."))), role: DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("forward-orbit-center"), Handle("forwardCenter"),
                H("A forward transported center"),
                StatementSource.FromAuthor(F.Disp(Transport(false))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("If the center belongs to an original domain, apply that generator isometry to its subspace representative. Its resulting point belongs to the complete orbit because the original orbit relation is transitive and contains this generator step. Membership proofs are retained only as subtype proofs."))), role: DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("backward-orbit-center"), Handle("backwardCenter"),
                H("An inverse transported center"),
                StatementSource.FromAuthor(F.Disp(Transport(true))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a center in an original range, use the inverse of the same supplied isometry. Symmetry of the full original relation puts the inverse image in the complete orbit. This construction includes self-identifications and all inverse generator moves."))), role: DescribeRole.Definition),
            Paragraph(Text("DevelopmentFamily(G,a,Y) is the dependent function type assigning a total source map D(i,c):X(i) to Y to every i and c in Center(G,a,i). Only its restriction to the ball of radius R around val(c) is controlled. Centered(G,a,D,o) means D(i,c)(val(c))=o for every i,c. LocalIso(G,a,D,R) means that for every i,c and x,y in X(i), the two inequalities edist(val(c),x)<R and edist(val(c),y)<R imply edist(D(i,c)(x),D(i,c)(y))=edist(x,y). The target Y has its own given extended metric and o is an element of Y. Nonnegative real radii are coerced into ENNReal in every distance comparison.")),
            Paragraph(Text("Compatible(G,a,D,R) has the following exact meaning. For every original generator j, every c in Center(G,a,src(j)), every membership proof h:val(c) in dom(j), and every x in dom(j) with edist(val(c),val(x))<R, D(src(j),c)(val(x)) equals D(dst(j),forwardCenter(G,a,j,c,h))(val(iso(j,x))). The compatibility is imposed on the original generator faces. Its inverse direction follows from the same equality and the inverse isometry; no arbitrary relation-wide compatibility is assumed.")),
            Paragraph(Text("Write Respects(G,F) for the assertion that Rel(G,b,c) implies F(b)=F(c) for every b,c. Agreement(G,a,D,F,t) means that for every i,c,x, edist(val(c),x)<t implies F(Point(i,x))=D(i,c)(x). Outside(G,a,F,o,t) means that F(b)=o whenever Nearby(G,a,t,b) is false. Saturated(G,a,t) means that Rel(G,b,c) implies Nearby(G,a,t,b) if and only if Nearby(G,a,t,c).")),
            Paragraph(Text("Finally Lower(G,a,D,r) means that for every x,y in A(X), every cx in Center(G,a,first(x)), and every cy in Center(G,a,first(y)), edist(val(cx),second(x))<r and edist(val(cy),second(y))<r imply edist(D(first(x),cx)(second(x)),D(first(y),cy)(second(y))) at most delta(G,x,y). Here delta(G,x,y) is exactly G.distance: the infimum, in ENNReal, of the costs of all literal original finite G.Chain derivations from x to y. A paid source move costs its original extended distance; either direction of an original generator costs zero. Infinite costs remain allowed in this infimum.")),
            Describe.Lean(DescribeId.Create("saturated-orbit-development-extension"), Handle("exists_saturated_extension"),
                H("A total extension and the original chain lower bound"),
                StatementSource.FromAuthor(F.Disp(Extension())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("J is finite and the single complete actual orbit of a is finite. I need not be finite, and there is no finiteness assumption on any source space. R is an arbitrary supplied positive nonnegative real radius. The theorem constructs r>0 with r+r+r<R and a total F:A(X) to Y satisfying Respects, Agreement on every radius-(r+r+r) source ball, Outside with value o, F(a)=o, Saturated, and Lower on the smaller radius-r balls. It assumes neither a total invariant map nor saturation, global continuity, global nonexpansion, or equality of a quotient distance with a target distance.")),
                    Paragraph(Text("For each original domain, separate its closed set from the finite set of orbit centers in that source that do not lie in the domain. Compact-closed separation gives a positive radius. Do the same for every original range. Finite minima over J give uniform incidence guards. To separate centers in the same source, take the positive extended infimum separation of that finite source fiber. Take a further finite minimum indexed by the actual tagged orbit, so no enumeration of I is needed. Cap all these bounds by R, choose a positive finite s strictly below their minimum, and put r=s/8. Then 3r<R, and 6r is smaller than every relevant center separation.")),
                    Paragraph(Text("If two radius-3r balls in the same source overlap at x, the triangle inequality gives a center distance below 6r. The separation bound forces their actual centers to be equal. Consequently the local value D(i,c)(x) is independent of the center selected for x. Empty source fibers cause no choice: they contain no tagged points, and a fiber with no orbit center contributes nothing to the union.")),
                    Paragraph(Text("Suppose x lies on an original generator face and within 3r of a source orbit center c. The domain guard puts c on that same face. Applying the original isometry transports c to an orbit center in the target and preserves its distance to the image of x. Thus the ball union is closed under every forward generator. The range guard and inverse isometry prove the corresponding inverse statement. These two constructions give equivalence of membership at the endpoints of each original step. Induction on the equivalence closure proves saturation for every pair in Rel.")),
                    Paragraph(Text("Define F at a point in this union using any nearby center and its source map D(i,c); define F=o elsewhere. Uniqueness of the center in each source proves Agreement. On a generator step inside the union, compatibility of the source maps proves equality of the two F-values. A step outside the union has both endpoints outside by the inverse membership implication, so both F-values are o. Induction on Rel then gives Respects globally. The centered condition gives F(a)=o.")),
                    Paragraph(Text("Agreement transfers each local isometry estimate for D to a nonexpansion estimate for F on the radius-3r source balls. The derived incidence guards and Respects therefore satisfy the hypotheses of ChainLocalDevelopment.local_development_distance_le. Applying that theorem gives the lower bound for the exact original chain infimum, and Agreement rewrites the endpoint values as the displayed D-values. No attainment or reverse distance comparison is asserted."))), role: DescribeRole.Theorem),
            Paragraph(Text("This theorem assembles supplied compatible developments. Constructing the actual hyperbolic source maps, proving their marked face compatibility, and establishing a finite complete orbit for a particular geometric gluing are separate geometric obligations. The extension may be discontinuous at the boundary of the ball union, which has no effect on the stated local estimate.")))));

    private static Formula G => Id("G");
    private static Formula a => Id("a");
    private static Formula A => Call("A", Id("X"));
    private static Formula Centers(Formula i) => Call("Center", G, a, i);
    private static Formula CenterStatement() => Base(All("i", Id("I"),
        All("c", Call("X", Id("i")), Iff(
            Call("Member", Id("c"), Call("UnderlyingSet", Centers(Id("i")))),
            Call("Rel", G, a, Call("Point", Id("i"), Id("c")))))));
    private static Formula Base(Formula body)
    {
        body = All("a", A, body);
        body = All("G", Call("Datum", Id("I"), Id("J"), Id("X")), body);
        body = F.Seq(F.OpenBracket, All("i", Id("I"), Call("EMetricSpace", Call("X", Id("i")))), F.CloseBracket, F.Sp, body);
        return All("I", Id("Types"), All("J", Id("Types"), All("X", new Formula.TypeArrow(Id("I"), Id("Types")), body)));
    }
    private static Formula Transport(bool inverse)
    {
        var j = Id("j"); var c = Id("c"); var h = Id("h");
        var source = Call(inverse ? "dst" : "src", G, j);
        var target = Call(inverse ? "src" : "dst", G, j);
        var face = Call(inverse ? "ran" : "dom", G, j);
        var name = inverse ? "backwardCenter" : "forwardCenter";
        var iso = Call(inverse ? "inverseIso" : "iso", G, j);
        var result = And(
            Call("Element", Call(name, G, a, j, c, h), Centers(target)),
            Eq(Call("val", Call(name, G, a, j, c, h)),
                Call("val", App(iso, Call("SubspacePoint", Call("val", c), h)))));
        return Base(All("j", Id("J"), All("c", Centers(source),
            All("h", Call("Member", Call("val", c), face), result))));
    }
    private static Formula Extension()
    {
        var D = Id("D"); var o = Id("o"); var R = Id("R");
        var r = Id("r"); var f = Id("F"); var t = Call("add", Call("add", r, r), r);
        var conclusion = Exists("r", Id("NNReal"), And(Lt(F.D(0), r), Lt(t, R),
            Exists("F", new Formula.TypeArrow(A, Id("Y")), And(
                Call("Respects", G, f), Call("Agreement", G, a, D, f, t),
                Call("Outside", G, a, f, o, t), Eq(App(f, a), o),
                Call("Saturated", G, a, t), Call("Lower", G, a, D, r)))));
        var hypotheses = And(Call("Finite", Call("Orbit", G, a)), Lt(F.D(0), R),
            Call("Centered", G, a, D, o), Call("LocalIso", G, a, D, R), Call("Compatible", G, a, D, R));
        var body = All("o", Id("Y"), All("D", Call("DevelopmentFamily", G, a, Id("Y")),
            All("R", Id("NNReal"), Implies(hypotheses, conclusion))));
        body = All("Y", Id("Types"), F.Seq(F.OpenBracket, Call("EMetricSpace", Id("Y")), F.CloseBracket, F.Sp, body));
        return Base(F.Seq(F.OpenBracket, Call("Fintype", Id("J")), F.CloseBracket, F.Sp, body));
    }
    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create("D5/S3/Topology/OrbitDevelopmentExtension." + name);
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [..xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [..xs]);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Exists(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula And(params Formula[] xs)
    {
        var r = xs[^1]; for (var i = xs.Length - 2; i >= 0; i--) r = new Formula.Logic(xs[i], FormulaLogicOperator.And, r); return r;
    }
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Lt(Formula x, Formula y) => F.Seq(x, F.Sp, F.Lt, F.Sp, y);
}
