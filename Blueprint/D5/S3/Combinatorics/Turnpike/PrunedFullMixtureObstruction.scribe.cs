using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Turnpike;

internal sealed class PrunedFullMixtureObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Turnpike/PrunedFullMixtureObstruction";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FiniteGeometry/elder2026turnpike");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full containment-pruned triangle LP has an assignment outside every finite convex mixture of actual real rulers for its input.",
        H("The full triangle LP does not equal the actual-ruler convex hull"),
        Blocks(
            Paragraph(Text("Elder, Marçais and Kingsford, WABI 2026, DOI 10.4230/LIPIcs.WABI.2026.20, Sections 3.1–3.5 and 5, supply the guarded ordered numerical relation, triangle marginal relaxation and containment context. Proposition 10 and System 11 are the marginal-system locators. The source is licensed CC BY 4.0. The universal same-entire-P finite-mixture assertion below is the repository research event; neither the assertion nor this refutation is attributed to a named published conjecture. The scalar endpoint-spine statement in Section 3.5 is a different assertion.")),
            Paragraph(Text("All indices below are zero-based, exactly as in Lean: vertices lie in Fin n, labels in Fin d, I(n) contains every pair (i,j) with i<j, and Delta(n) contains every triple i<j<k. The complete ordered relation R(y,mu) contains every label triple (a,b,c) satisfying y_a+y_b=y_c and (a≠b or mu_a≥2); both orders of distinct summands remain. In formulas triple(r) is the underlying triple of a relation member. coordinate(0,r), coordinate(1,r), coordinate(2,r) select its first, second and outer labels; edge(tau,0), edge(tau,1), edge(tau,2) select ij,jk,ik.")),
            Paragraph(Text("The closed multiplicity-rank-block intersection mask is A(e,q)=rankMask(mu,e,q). For e=(i,j), its value is one precisely when (i+1)(n−j)≤sum_{r≤q}mu_r and 1+sum_{r<q}mu_r≤choose(n,2)−choose(j−i+1,2)+1; otherwise it is zero. These are the original rank bounds, with no extra pruning or endpoint restriction.")),
            Paragraph(Text("Realizes(y,mu,x) means strict increase of the real-valued ruler, a numerical label for every interval difference, and exactly mu_q occurrences of y_q for every label. The formulas below expand these conditions as well as the full feasible system and the finite convex mixture. indicator(E) is one if E is true and zero otherwise. Cardinalities are expressed as finite sums of these indicators.")),
            Describe.Lean(DescribeId.Create("turnpike-pruned-full-mixture-claim"), DeclarationHandle.Create(Module + ".claim"),
                H("The unchanged universal finite-actual-mixture event"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Q("claim"),Q("Prop")),Par(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Every n≥3, d≥1, strictly decreasing positive real input y and positive natural multiplicity function mu with total choose(n,2) is quantified. Existence of an actual real realizing ruler is retained as an input premise. Every entire P with its own existential full T is quantified. T has every one of the choose(n,3) triangles, all complete guarded relation entries, product-mask bounds, normalization and all three marginals against that same entire P. Each mixture has arbitrary finite K>0, real nonnegative weights of total one, and arbitrary real actual rulers for exactly the same whole input. Translation and reflection are unrestricted; there is no selected-realizer restriction, integrality premise, global joint distribution, spine substitution, scalar projection or additional presolve."))), DescribeRole.Definition),
            Paragraph(Text("The exact witness has n=7, d=9, y=(9,8,7,6,5,4,3,2,1) and mu=(1,1,2,1,3,3,3,4,3). The actual ruler (0,1,2,4,5,7,9) is strictly increasing and has exactly this entire distance multiset, whose total is 21. The certificate uses denominator four. All 43 positive P entries and all 98 positive T atoms in its 35 triangle blocks are listed below; every omitted coordinate is exactly zero. No part of the proposed realizer catalog is needed by the proof.")),
            Paragraph(Text("Complete P: an interval i,j followed by q:mass lists its nonzero label masses. 0,1 7:1/2,8:1/2; 0,2 5:1/4,6:1/2,7:1/4; 0,3 4:1/2,5:1/2; 0,4 2:1/4,3:1/2,4:1/4; 0,5 1:1/2,2:1/2; 0,6 0:1; 1,2 7:1/2,8:1/2; 1,3 6:1; 1,4 4:1/2,5:1/2; 1,5 2:1/2,4:1/2; 1,6 1:1/2,2:1/2; 2,3 7:1/2,8:1/2; 2,4 6:1; 2,5 4:1/2,5:1/2; 2,6 2:1/4,3:1/2,4:1/4; 3,4 7:1/2,8:1/2; 3,5 5:1/2,7:1/2; 3,6 4:1/2,5:1/2; 4,5 7:1/2,8:1/2; 4,6 5:1/4,6:1/2,7:1/4; 5,6 7:1/2,8:1/2")),
            Paragraph(Text("Complete full T: a triangle i,j,k followed by a,b,c:mass lists its nonzero ordered relation atoms. 0,1,2 7,7,5:1/4 7,8,6:1/4 8,7,6:1/4 8,8,7:1/4; 0,1,3 7,6,4:1/2 8,6,5:1/2; 0,1,4 7,4,2:1/4 7,5,3:1/4 8,4,3:1/4 8,5,4:1/4; 0,1,5 7,4,2:1/2 8,2,1:1/2; 0,1,6 7,2,0:1/2 8,1,0:1/2; 0,2,3 5,8,4:1/4 6,7,4:1/4 6,8,5:1/4 7,7,5:1/4; 0,2,4 5,6,2:1/4 6,6,3:1/2 7,6,4:1/4; 0,2,5 5,5,1:1/4 6,4,1:1/4 6,5,2:1/4 7,4,2:1/4; 0,2,6 5,4,0:1/4 6,3,0:1/2 7,2,0:1/4; 0,3,4 4,7,2:1/4 4,8,3:1/4 5,7,3:1/4 5,8,4:1/4; 0,3,5 4,7,2:1/2 5,5,1:1/2; 0,3,6 4,5,0:1/2 5,4,0:1/2; 0,4,5 2,8,1:1/4 3,7,1:1/4 3,8,2:1/4 4,7,2:1/4; 0,4,6 2,7,0:1/4 3,6,0:1/2 4,5,0:1/4; 0,5,6 1,8,0:1/2 2,7,0:1/2; 1,2,3 7,8,6:1/2 8,7,6:1/2; 1,2,4 7,6,4:1/2 8,6,5:1/2; 1,2,5 7,4,2:1/2 8,5,4:1/2; 1,2,6 7,3,1:1/4 7,4,2:1/4 8,2,1:1/4 8,3,2:1/4; 1,3,4 6,7,4:1/2 6,8,5:1/2; 1,3,5 6,5,2:1/2 6,7,4:1/2; 1,3,6 6,4,1:1/2 6,5,2:1/2; 1,4,5 4,7,2:1/2 5,8,4:1/2; 1,4,6 4,6,1:1/4 4,7,2:1/4 5,5,1:1/4 5,6,2:1/4; 1,5,6 2,8,1:1/2 4,7,2:1/2; 2,3,4 7,8,6:1/2 8,7,6:1/2; 2,3,5 7,7,5:1/2 8,5,4:1/2; 2,3,6 7,4,2:1/4 7,5,3:1/4 8,4,3:1/4 8,5,4:1/4; 2,4,5 6,7,4:1/2 6,8,5:1/2; 2,4,6 6,5,2:1/4 6,6,3:1/2 6,7,4:1/4; 2,5,6 4,7,2:1/4 4,8,3:1/4 5,7,3:1/4 5,8,4:1/4; 3,4,5 7,7,5:1/2 8,8,7:1/2; 3,4,6 7,6,4:1/4 7,7,5:1/4 8,5,4:1/4 8,6,5:1/4; 3,5,6 5,8,4:1/2 7,7,5:1/2; 4,5,6 7,7,5:1/4 7,8,6:1/4 8,7,6:1/4 8,8,7:1/4")),
            Paragraph(Text("PrunedFullMixtureData checks the fixed natural numerators directly in Lean: row totals four, label-column totals four times mu, bounds and every rank mask; every raw atom satisfies exact addition and the repeated-label guard; positive raw atoms satisfy the product mask; every triangle has total numerator four and all three exact marginal numerators. weightedAtoms, weightedAtoms_sum and weightedAtoms_marginal from PrunedTriangleLP turn these finite tables into the original real T on the entire relation, with no assumption that a listed support is exhaustive of R. Blocks with fewer than four atoms are padded by zero-weight copies of a valid atom.")),
            Describe.Lean(DescribeId.Create("turnpike-pruned-full-mixture-result"), DeclarationHandle.Create(Module + ".result"),
                H("Literal refutation of the universal event"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Par(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("For every real x realizing this input, x_2−x_0 differs from y_6=3. The proof translates by x_0. Every normalized coordinate except the initial zero is one of the positive integer input labels, hence is a natural number at most nine. Strict increase transfers to these natural coordinates, and every interval-difference histogram transfers exactly. If the second noninitial coordinate were three, every normalized ruler would be (0,a,3,b,c,d,f), with 1≤a≤2, 4≤b≤6, b+1≤c≤7, c+1≤d≤8 and d+1≤f≤9. The kernel checks all 30 such bounded configurations and proves that none has the required entire histogram. This finite obstruction is exhaustive under the stated hypothesis and does not classify or restrict other actual realizers.")),
                    Paragraph(Text("The certificate has P[(0,2),6]=1/2. Every actual realizer has indicator(x_2−x_0=y_6)=0 by the universal forbidden-observation theorem, so for every K>0 and every proposed family of real realizers, the corresponding weighted coordinate sum is zero. The equation required of the same entire P would therefore imply 1/2=0. The generic mixture_forbidden lemma carries this argument through arbitrary real weights; the ActualMixture predicate still retains their nonnegativity and normalization. The live proof uses the fixed certificate and the universal real-to-natural histogram bridge. Fractionality alone is not the obstruction.")),
                    Paragraph(Text("This is a finite-instance refutation of this precise full containment-pruned event. It makes no minimum-size, minimum-denominator, universal-family, algorithmic-performance, published-priority, strict Omega replay or complete-realizer-classification claim. Canonical report, emission, freezing and independent review are separate publication checks."))), DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        Formula body = All("P",Arrow(I(),Arrow(Fin("d"),Real())),Imp(FullFeasibleBody(),MixtureBody()));
        body = Imp(Some("r",Arrow(Fin("n"),Real()),RealizesBody(X("r"))),body);
        body = Imp(Equal(SumOver("q",Fin("d"),App(X("mu"),X("q"))),App(Q("choose"),X("n"),D(2))),body);
        body = Imp(All("q",Fin("d"),LT(D(0),App(X("mu"),X("q")))),body);
        body = Imp(All("q",Fin("d"),LT(D(0),App(X("y"),X("q")))),body);
        body = Imp(All("a",Fin("d"),All("b",Fin("d"),Imp(LT(X("a"),X("b")),LT(App(X("y"),X("b")),App(X("y"),X("a")))))),body);
        body = Imp(LE(D(1),X("d")),body);
        body = Imp(LE(D(3),X("n")),body);
        return All("n",Nat(),All("d",Nat(),All("y",Arrow(Fin("d"),Real()),All("mu",Arrow(Fin("d"),Nat()),body))));
    }
    private static Formula RealizesBody(Formula x)
    {
        Formula increasing = All("i",Fin("n"),All("j",Fin("n"),Imp(LT(X("i"),X("j")),LT(App(x,X("i")),App(x,X("j"))))));
        Formula difference = Difference(x,X("e"));
        Formula labels = All("e",I(),Some("q",Fin("d"),Equal(difference,App(X("y"),X("q")))));
        Formula counts = All("q",Fin("d"),Equal(SumOver("e",I(),Indicator(Equal(difference,App(X("y"),X("q"))))),App(X("mu"),X("q"))));
        return And(increasing,And(labels,counts));
    }
    private static Formula FullFeasibleBody()
    {
        Formula p = App(X("P"),X("e"),X("q"));
        Formula bounds = All("e",I(),All("q",Fin("d"),And(LE(D(0),p),And(LE(p,D(1)),LE(p,App(Q("rankMask"),X("mu"),X("e"),X("q")))))));
        Formula rows = All("e",I(),Equal(SumOver("q",Fin("d"),p),D(1)));
        Formula columns = All("q",Fin("d"),Equal(SumOver("e",I(),p),App(X("mu"),X("q"))));
        Formula t = App(X("T"),X("tau"),X("r"));
        Formula masks = Multiply(Multiply(Mask(0),Mask(1)),Mask(2));
        Formula block = And(All("r",R(),And(LE(D(0),t),And(LE(t,D(1)),LE(t,masks)))),
            And(Equal(SumOver("r",R(),t),D(1)),And(Marginal(0),And(Marginal(1),Marginal(2)))));
        Formula full = Some("T",Arrow(Delta(),Arrow(R(),Real())),All("tau",Delta(),block));
        return And(bounds,And(rows,And(columns,full)));
    }
    private static Formula MixtureBody()
    {
        Formula ktype = Fin("K");
        Formula xk = App(X("x"),X("k"));
        Formula coordinate = Equal(App(X("P"),X("e"),X("q")),
            SumOver("k",ktype,Multiply(App(X("w"),X("k")),Indicator(Equal(Difference(xk,X("e")),App(X("y"),X("q")))))));
        Formula body = And(All("k",ktype,LE(D(0),App(X("w"),X("k")))),
            And(Equal(SumOver("k",ktype,App(X("w"),X("k"))),D(1)),
            And(All("k",ktype,RealizesBody(xk)),All("e",I(),All("q",Fin("d"),coordinate)))));
        return Some("K",Nat(),And(LT(D(0),X("K")),Some("w",Arrow(ktype,Real()),Some("x",Arrow(ktype,Arrow(Fin("n"),Real())),body))));
    }
    private static Formula Marginal(byte u) => All("q",Fin("d"),Equal(
        SumOver("r",R(),Multiply(Indicator(Equal(Coordinate(u),X("q"))),App(X("T"),X("tau"),X("r")))),
        App(X("P"),Edge(u),X("q"))));
    private static Formula Coordinate(byte u) => App(Q("coordinate"),D(u),App(Q("triple"),X("r")));
    private static Formula Edge(byte u) => App(Q("edge"),X("tau"),D(u));
    private static Formula Mask(byte u) => App(Q("rankMask"),X("mu"),Edge(u),Coordinate(u));
    private static Formula Difference(Formula x,Formula e) => Subtract(App(x,App(Q("right"),e)),App(x,App(Q("left"),e)));
    private static Formula Indicator(Formula p) => App(Q("indicator"),p);
    private static Formula I() => App(Q("Interval"),X("n"));
    private static Formula Delta() => App(Q("Triangle"),X("n"));
    private static Formula R() => App(Q("Relation"),X("y"),X("mu"));
    private static Formula Fin(string n) => App(Q("Fin"),X(n));
    private static Formula Nat() => Q("Nat");
    private static Formula Real() => Q("Real");
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula App(Formula f,params Formula[] args) => new Formula.Apply(f,[..args]);
    private static Formula Par(Formula x) => Seq(Left,Open,x,Right,Close);
    private static Formula Typed(Formula a,Formula b) => Par(Seq(a,Colon,Sp,b));
    private static Formula All(string v,Formula t,Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(v),t,b);
    private static Formula Some(string v,Formula t,Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(v),t,b);
    private static Formula SumOver(string v,Formula t,Formula b) => Seq(new Formula.Subscript(Sum,Seq(X(v),Colon,Sp,t)),Sp,Par(b));
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula LT(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula LE(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Multiply(Formula a,Formula b) => new Formula.Binary(Par(a),FormulaBinaryOperator.Multiply,Par(b));
    private static Formula X(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(Operatorname,Grp(F.Id(n)));
}
