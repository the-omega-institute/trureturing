using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Turnpike;

internal sealed class DistinctFullMixtureObstructionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Turnpike/DistinctFullMixtureObstruction";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FiniteGeometry/elder2026turnpike");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-distinct full containment-pruned triangle LP has an assignment outside every finite convex mixture of actual real rulers for its input.",
        H("The all-distinct full triangle LP does not equal the actual-ruler convex hull"),
        Blocks(
            Paragraph(Text("Elder, Marçais and Kingsford, WABI 2026, DOI 10.4230/LIPIcs.WABI.2026.20, Sections 3.1–3.5 and 5, supply the guarded ordered numerical relation, triangle marginal relaxation and containment context. Proposition 10 and System 11 are the marginal-system locators. The source is licensed CC BY 4.0. The finite-mixture assertion below concerns every coordinate of the same assignment.")),
            Paragraph(Text("All indices below are zero-based, exactly as in Lean: vertices lie in Fin n, labels in Fin d, I(n) contains every pair (i,j) with i<j, and Delta(n) contains every triple i<j<k. The complete ordered relation R(y,mu) contains every label triple (a,b,c) satisfying y_a+y_b=y_c and (a≠b or mu_a≥2); both orders of distinct summands remain. In formulas triple(r) is the underlying triple of a relation member. coordinate(0,r), coordinate(1,r), coordinate(2,r) select its first, second and outer labels; edge(tau,0), edge(tau,1), edge(tau,2) select ij,jk,ik.")),
            Paragraph(Text("The closed multiplicity-rank-block intersection mask is A(e,q)=rankMask(mu,e,q). For e=(i,j), its value is one precisely when (i+1)(n−j)≤sum_{r≤q}mu_r and 1+sum_{r<q}mu_r≤choose(n,2)−choose(j−i+1,2)+1; otherwise it is zero. These are the original rank bounds, with no extra pruning or endpoint restriction.")),
            Paragraph(Text("Realizes(y,mu,x) means strict increase of the real-valued ruler, a numerical label for every interval difference, and exactly mu_q occurrences of y_q for every label. The formulas below expand these conditions as well as the full feasible system and the finite convex mixture. indicator(E) is one if E is true and zero otherwise. Cardinalities are expressed as finite sums of these indicators.")),
            Describe.Lean(DescribeId.Create("turnpike-distinct-full-mixture-claim"), DeclarationHandle.Create(Module + ".claim"),
                H("The universal finite-actual-mixture assertion for distinct distances"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Q("claim"),Q("Prop")),Par(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Every n≥3, d≥1, strictly decreasing positive real input y and natural multiplicity function mu identically one with total choose(n,2) is quantified. Existence of an actual real realizing ruler is retained as an input premise. Every entire P with its own existential full T is quantified. T has every one of the choose(n,3) triangles, all complete guarded relation entries, product-mask bounds, normalization and all three marginals against that same entire P. Each mixture has arbitrary finite K>0, real nonnegative weights of total one, and arbitrary real actual rulers for exactly the same whole input. Translation and reflection are unrestricted; there is no selected-realizer restriction, integrality premise, global joint distribution, spine substitution, scalar projection or additional presolve."))), DescribeRole.Definition),
            Paragraph(Text("The input has n=6, d=15, y=(17,16,13,12,11,10,9,8,7,6,5,4,3,2,1) and mu_q=1 for every q. The ruler (0,1,4,10,12,17) realizes the entire input: its fifteen interval differences are exactly the fifteen listed labels, each once.")),
            Paragraph(Text("The following complete assignment uses denominator four. Each interval i,j is followed by its positive q:mass entries; every omitted entry is zero. The table specifies all 225 coordinates: 0,1 10:1/4,11:1/4,14:1/2; 0,2 7:1/4,8:1/4,9:1/4,11:1/4; 0,3 2:1/4,4:1/4,5:1/4,6:1/4; 0,4 1:1/2,2:1/4,3:1/4; 0,5 0:1; 1,2 9:1/4,12:1/2,13:1/4; 1,3 5:1/4,6:1/4,7:1/4,10:1/4; 1,4 3:1/2,4:1/2; 1,5 1:1/2,2:1/4,3:1/4; 2,3 8:1/2,13:1/2; 2,4 5:1/4,6:1/4,7:1/4,10:1/4; 2,5 2:1/4,4:1/4,5:1/4,6:1/4; 3,4 9:1/4,12:1/2,13:1/4; 3,5 7:1/4,8:1/4,9:1/4,11:1/4; 4,5 10:1/4,11:1/4,14:1/2.")),
            Paragraph(Text("The following twenty triangle blocks specify every positive ordered relation atom a,b,c:mass; every other atom of the full numerical relation has weight zero: 0,1,2 10,12,7:1/4 11,13,9:1/4 14,9,8:1/4 14,12,11:1/4; 0,1,3 10,7,2:1/4 11,10,6:1/4 14,5,4:1/4 14,6,5:1/4; 0,1,4 10,4,1:1/4 11,3,1:1/4 14,3,2:1/4 14,4,3:1/4; 0,1,5 10,3,0:1/4 11,2,0:1/4 14,1,0:1/2; 0,2,3 7,13,5:1/4 8,13,6:1/4 9,8,2:1/4 11,8,4:1/4; 0,2,4 7,10,2:1/4 8,6,1:1/4 9,5,1:1/4 11,7,3:1/4; 0,2,5 7,6,0:1/4 8,5,0:1/4 9,4,0:1/4 11,2,0:1/4; 0,3,4 2,12,1:1/4 4,13,2:1/4 5,9,1:1/4 6,12,3:1/4; 0,3,5 2,11,0:1/4 4,9,0:1/4 5,8,0:1/4 6,7,0:1/4; 0,4,5 1,14,0:1/2 2,11,0:1/4 3,10,0:1/4; 1,2,3 9,13,7:1/4 12,8,5:1/4 12,13,10:1/4 13,8,6:1/4; 1,2,4 9,10,4:1/4 12,6,3:1/4 12,7,4:1/4 13,5,3:1/4; 1,2,5 9,5,1:1/4 12,2,1:1/4 12,6,3:1/4 13,4,2:1/4; 1,3,4 5,13,3:1/4 6,12,3:1/4 7,12,4:1/4 10,9,4:1/4; 1,3,5 5,9,1:1/4 6,8,1:1/4 7,11,3:1/4 10,7,2:1/4; 1,4,5 3,11,1:1/4 3,14,2:1/4 4,10,1:1/4 4,14,3:1/4; 2,3,4 8,12,5:1/4 8,13,6:1/4 13,9,7:1/4 13,12,10:1/4; 2,3,5 8,9,2:1/4 8,11,4:1/4 13,7,5:1/4 13,8,6:1/4; 2,4,5 5,14,4:1/4 6,14,5:1/4 7,10,2:1/4 10,11,6:1/4; 3,4,5 9,14,8:1/4 12,10,7:1/4 12,14,11:1/4 13,11,9:1/4.")),
            Paragraph(Text("The natural numerators have row sums four and label-column sums four, lie between zero and four, and vanish outside the closed multiplicity-block intersection mask. Each displayed atom satisfies y_a+y_b=y_c with a distinct from b. Every positive atom satisfies all three rank masks. Each triangle has total numerator four and all three marginal numerators equal those of the same entire assignment. A block with three positive atoms is padded by a zero-weight copy of a valid atom. The weightedAtoms construction on the original complete relation, together with weightedAtoms_sum and weightedAtoms_marginal, gives real nonnegative weights, total one and all 900 required triangle marginals. Their upper bound one follows from nonnegativity and normalization; the product bound follows from the support masks.")),
            Describe.Lean(DescribeId.Create("turnpike-distinct-full-mixture-result"), DeclarationHandle.Create(Module + ".result"),
                H("Literal refutation of the universal event"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Par(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("For every real ruler x realizing this input, x_3−x_2 differs from y_8=7. Subtract x_0 from every coordinate. Each noninitial coordinate is an input label because it is the difference on interval (0,i), so it is an integer between one and seventeen. The initial coordinate becomes zero. Strict increase and all fifteen interval-difference histograms transfer exactly to the resulting natural coordinates z.")),
                    Paragraph(Text("If z_3−z_2=7, write z=(0,a,b,b+7,d,f). Strict increase and the bound seventeen give 1≤a≤7, a+1≤b≤8, b+8≤d≤16 and d+1≤f≤17. These bounds contain exactly 210 configurations. For each such configuration, at least one of the counts of distances 6, 5, 1 and 3 differs from one. The finite histogram calculation therefore excludes every such configuration, using necessary counts from the entire input. It assumes no classification or selected catalog of realizing rulers.")),
                    Paragraph(Text("The feasible assignment has P[(2,3),8]=1/2. For every actual real ruler realizing this same input, the corresponding indicator of x_3−x_2=7 is zero. Thus every finite convex mixture of arbitrary such real rulers has coordinate zero there. The mixture equation for this entire assignment would give 1/2=0, a contradiction. The generic mixture_forbidden theorem supplies this final implication. This refutes the stated universal assertion while retaining its realizability premise and its restriction that every distance multiplicity is one."))), DescribeRole.Theorem))));

    private static Formula ClaimBody()
    {
        Formula body = All("P",Arrow(I(),Arrow(Fin("d"),Real())),Imp(FullFeasibleBody(),MixtureBody()));
        body = Imp(Some("r",Arrow(Fin("n"),Real()),RealizesBody(X("r"))),body);
        body = Imp(All("q",Fin("d"),Equal(App(X("mu"),X("q")),D(1))),body);
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
