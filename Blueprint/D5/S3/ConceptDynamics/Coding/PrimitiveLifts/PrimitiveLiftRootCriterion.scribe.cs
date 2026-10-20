using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class PrimitiveLiftRootCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. v], f);
    private static Formula And(Formula a, Formula b) => Seq(Open,a,Sp,Land,Sp,b,Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Implies,Sp,Open,b,Close,Close);
    private static Formula Iff(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,F.Iff,Sp,Open,b,Close,Close);
    private static Formula Add(Formula a, Formula b) => Seq(Open,a,Plus,b,Close);
    private static Formula Mul(Formula a, Formula b) => Call("mul",a,b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
    private static Formula Group(Formula f, bool finite = false) => Q(Seq(
        OpenBracket,Call("Group",I("H")),CloseBracket,
        finite ? Seq(OpenBracket,Call("Fintype",I("H")),CloseBracket) : Seq(),f),B("H",I("Type")));
    private static Formula Atlas(Formula f, params Formula.BoundVariable[] rest) => Group(Q(f,
        [B("X",I("Type")),B("A",Call("ReturnAtlas",I("H"),I("X"))),.. rest]));
    private static Formula Period => Call("period",I("A"));
    private static Formula G => Call("holonomy",I("A"));
    private static Formula Point(Formula t, Formula z) => Call("point",I("A"),t,z);
    private static Formula Param => Call("Prod",Call("Fin",Period),I("H"));
    private static Formula First(Formula q) => Call("val",Call("first",q));
    private static Formula Second(Formula q) => Call("second",q);
    private static Formula Law(Formula q) => And(Call("Commute",Second(q),G),Q(
        Equal(App(I("f"),Point(I("t"),I("z"))),Point(Add(I("t"),First(q)),Mul(I("z"),Second(q)))),
        B("t",I("Int")),B("z",I("H"))));
    private static Formula Actual(Formula f, params Formula.BoundVariable[] rest) => Group(Q(f,
        [B("n",I("Nat")),B("C",Call("GroupMat",I("H"),I("n"),I("n"))),
        B("p",Call("Path",I("C"))),B("d",I("Nat")),..rest]));
    private static Formula Min => Equal(Call("minimalPeriod",Call("baseShift",I("C")),I("p")),I("d"));
    private static Formula Hist => Call("History",Call("expandedGraph",I("C")));
    private static Formula Lift => Call("LiftOrbit",I("C"),I("p"),I("d"));
    private static DocumentBlock Item(string selector, string title, Formula formula, string text,
        DescribeRole role) => Describe.Lean(DescribeId.Create("primitive-lift-"+
            selector.Replace(".","-").Replace("_","-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix+selector),H(title),StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A primitive base orbit retains an ordered group return invisible to ordinary periodic counts.",
        H("Equivariant roots on actual primitive lifts"),Blocks(
        Item("ReturnAtlas","Complete signed return charts",Group(Q(
            Seq(Call("ReturnAtlas",I("H"),I("X")),Colon,I("Type")),B("X",I("Type")))),
            "ReturnAtlas H X contains d>0, g:H, a surjective point:Int->H->X, time and the left deck action. Its exact equality law is point(t,z)=point(s,w) iff there is an integer m with t=s+d*m and z*g^m=w. The time and deck laws are time(point(t,z))=point(t+1,z) and deck(a,point(t,z))=point(t,a*z). No commutativity or finiteness assumption on H is imposed by this structure. The signed relation is a complete equality criterion, rather than an assumed classification of equivariant maps.",DescribeRole.Definition),
        Item("coordinates","All phases and all group coordinates",Atlas(
            Call("Equiv",Param,I("X"))),
            "The equivalence sends (q,z) to point(q.val,z), with q in Fin d. Injectivity uses the exact return relation and the strict phase bounds. Surjectivity reduces any integer t by Euclidean division, replacing z with z*g^(t/d). This includes negative times and every group coordinate.",DescribeRole.Definition),
        Item("Equivariant","The specified left deck action",Atlas(Q(
            Equal(Call("Equivariant",I("A"),I("f")),Q(Equal(
                App(I("f"),Call("deck",I("A"),I("a"),I("x"))),
                Call("deck",I("A"),I("a"),App(I("f"),I("x")))),
                B("a",I("H")),B("x",I("X")))),B("f",Call("Map",I("X"),I("X"))))),
            "Equivariance always uses multiplication on the left. The holonomy seam acts on the right; these two operations are kept distinct for nonabelian groups.",DescribeRole.Definition),
        Item("normal_form","Unique reverse classification",Atlas(Imp(And(
            Call("Equivariant",I("A"),I("f")),Call("FunctionCommute",I("f"),Call("time",I("A")))),
            Ex(And(Law(I("q")),Q(Imp(Law(I("r")),Equal(I("r"),I("q"))),B("r",Param))),B("q",Param))),
            B("f",Call("Map",I("X"),I("X")))),
            "For every deck-equivariant f commuting with time there is exactly one q=(s,b) in Fin d times H such that b commutes with g and f(point(t,z))=point(t+s,z*b) for every signed t and z. Read f(point(0,1)) in the complete coordinates. Equivariance and time commutation propagate this image in both time directions; time injectivity is derived from the return relation. Comparing the two images of point(d,1)=point(0,g) forces b*g=g*b. Finally the image of point(0,1) proves uniqueness. In the finite phase coordinates this is T^s composed with the right map R_b.",DescribeRole.Theorem),
        Item("normalMap","Constructed maps on the same carrier",Atlas(Q(
            Equal(Call("normalMap",I("A"),I("s"),I("b"),I("x")),
                Point(Add(First(Call("inverseCoordinates",I("A"),I("x"))),I("s")),
                    Mul(Second(Call("inverseCoordinates",I("A"),I("x"))),I("b")))),
            B("s",I("Int")),B("b",I("H")),B("x",I("X")))),
            "The definition uses the existing carrier X and its complete coordinate equivalence. When b commutes with g, its value on every signed coordinate is point(t+s,z*b); the seam constraint proves independence of the chosen representative. Iteration gives point(t+k*s,z*b^k), which is used in the root construction.",DescribeRole.Definition),
        Item("normalEquiv","Lawful normal maps are permutations",Atlas(Q(Imp(
            Call("Commute",I("b"),G),Seq(Call("normalEquiv",I("A"),I("s"),I("b")),Colon,Call("Perm",I("X")))),B("s",I("Int")),B("b",I("H")))),
            "normalEquiv(s,b) has normalMap(s,b) as its forward function and normalMap(-s,inverse(b)) as its inverse. The complete signed-coordinate law proves both inverse identities. Thus the normal form also implies that every deck-equivariant map commuting with time is bijective. The root criterion constructs its sufficient witness using this permutation.",DescribeRole.Definition),
        Item("root_criterion","Exact root equation with a signed seam exponent",Atlas(Iff(
            Ex(And(Call("Equivariant",I("A"),I("f")),Equal(Call("iterate",I("f"),I("k")),Call("time",I("A")))),B("f",Call("Map",I("X"),I("X")))),
            Ex(And(Call("Commute",I("b"),G),And(Equal(Mul(I("k"),Call("val",I("s"))),Add(D(1),Mul(Period,I("m")))),
                Equal(Mul(Pow(I("b"),I("k")),Pow(G,I("m"))),D(1)))),
                B("s",Call("Fin",Period)),B("m",I("Int")),B("b",I("H")))),B("k",I("Nat"))),
            "For each natural k, a deck-equivariant f with f iterated k times equal to time exists exactly when there are s:Fin d, m:Int and b:H with b*g=g*b, k*s.val=1+d*m and b^k*g^m=1. In particular this gives every positive root order requested. The root equation implies time commutation, so no such premise is added to root existence. The necessity uses the reverse normal form and then the exact return relation. The sufficiency constructs normalMap(s.val,b) on X and checks its kth iterate on every coordinate. At d=1 the canonical phase is zero and m=-1, giving b^k=g. Restricting m to natural numbers would lose precisely this case.",DescribeRole.Theorem),
        Item("orbitHolonomy","Actual ordered loop label",Actual(Equal(Call("orbitHolonomy",I("C"),I("p"),I("d")),
            Call("totalLabel",Call("historyWindow",Call("baseGraph",I("C")),I("p"),D(0),I("d"))))),
            "The loop retains the original numbered edges and their time order. For d equal to the minimal positive base period its endpoints agree. Its total label equals the coordinate at time d of anchoredHistory(p,1), proved by comparing prefixLabel with the existing ordered positiveLabels list.",DescribeRole.Definition),
        Item("LiftOrbit","Every lift of one specified base orbit",Actual(Equal(Lift,
            Call("Subtype",Hist,Call("liesOverForwardPhase",I("C"),I("p"),I("d"))))),
            "LiftOrbit C p d consists exactly of actual History(expandedGraph C) whose forgetHistory equals the qth base shift of p for some q:Fin d. liesOverForwardPhase denotes this existential predicate. No history is discarded inside a fibre. The construction is local to this base orbit; a global map on several base orbits can permute them.",DescribeRole.Definition),
        Item("actualAtlas","Actual histories realize the complete return relation",Actual(Imp(And(
            Call("Positive",I("d")),Min),Call("ReturnAtlas",I("H"),Lift))),
            "The constructed atlas has period d, holonomy equal to the actual loop label, time equal to the restricted original one-step shift, and deck equal to groupHistory. Its point(t,z) is groupHistory(z,translate(t,anchoredHistory(p,1))). The existing anchoredEquiv proves that all actual lifts are covered. The existing signed_recovery theorem supplies the full positive and negative return law. Euclidean reduction and mathlib's injectivity of iterates below the minimal period separate phases. Comparing the remaining group coordinates yields the exact relation point(t,z)=point(s,w) iff t=s+d*m and z*g^m=w. Thus the reverse classification and root criterion apply to this actual history subsystem, with no separately assumed finite model. The actual bridge, like the abstract return argument, requires neither finiteness nor commutativity of H. This is a repository synthesis of the classical ordered voltage-return and regular-action mechanisms; no claim of new mathematics in the literature is made.",DescribeRole.Definition))));
}
