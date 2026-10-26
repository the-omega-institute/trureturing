using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class TwoOrbitSquareRootCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/PrimitiveLifts/TwoOrbitSquareRootCriterion.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. v], f);
    private static Formula And(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula Or(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Lor,Sp,Open,b,Close,Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Implies,Sp,Open,b,Close,Close);
    private static Formula Iff(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,F.Iff,Sp,Open,b,Close,Close);
    private static Formula Mul(Formula a, Formula b) => Call("mul",a,b);
    private static Formula Add(Formula a, Formula b) => Seq(Open,a,Plus,b,Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
    private static Formula Hist => Call("History",Call("expandedGraph",I("C")));
    private static Formula Union => Call("OrbitUnion",I("C"),I("P"),I("Q"));
    private static Formula Time => Call("unionShift",I("C"),I("P"),I("Q"));
    private static Formula Deck(Formula a, Formula x) => Call("unionDeck",I("C"),I("P"),I("Q"),a,x);
    private static Formula Translate(Formula t, Formula p) => Call("translate",Call("baseGraph",I("C")),t,p);
    private static Formula Orbit(Formula p) => Ex(Equal(Call("forgetHistory",I("x")),Translate(I("t"),p)),B("t",I("Int")));
    private static Formula Hol(Formula p, Formula d) => Call("orbitHolonomy",I("C"),p,d);
    private static Formula Local(Formula p, Formula d) => Ex(And(
        Call("Commute",I("b"),Hol(p,d)),And(
        Equal(Mul(D(2),Call("intCast",Call("val",I("s")))),Add(D(1),Mul(Call("intCast",d),I("m")))),
        Equal(Mul(Pow(I("b"),D(2)),Pow(Hol(p,d),I("m"))),D(1)))),
        B("s",Call("Fin",d)),B("m",I("Int")),B("b",I("H")));
    private static Formula Scope(Formula f, params Formula.BoundVariable[] rest) => Q(Seq(
        OpenBracket,Call("Group",I("H")),CloseBracket,Q(f,
        [B("n",I("Nat")),B("C",Call("GroupMat",I("H"),I("n"),I("n"))),
        B("P",Call("Path",I("C"))),B("Q",Call("Path",I("C"))),..rest])),B("H",I("Type")));
    private static Formula Minimal(Formula p, Formula d) => Equal(Call("minimalPeriod",Call("baseShift",I("C")),p),d);
    private static DocumentBlock Item(string selector, string title, Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("two-orbit-"+selector.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+selector),H(title),StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two primitive base orbits can jointly admit an equivariant square root even when separate roots fail.",
        H("Square roots on two full actual lift orbits"),Blocks(
        Item("OrbitUnion","All original histories over both signed base orbits",Scope(Equal(Union,
            Seq(OpenBrace,I("x"),Colon,Hist,Sp,Mid,Sp,Or(Orbit(I("P")),Orbit(I("Q"))),CloseBrace))),
            "OrbitUnion C P Q is the subtype of every original bilateral legal history of expandedGraph C whose forgotten numbered-edge base history is translate(t,P) or translate(t,Q) for an integer t. The two alternatives retain all group coordinates and all original numbered edges. Neither a representative lift nor a selected subset of a fibre replaces this carrier.",DescribeRole.Definition),
        Item("unionShift","The original time map restricted to the union",Scope(Q(
            Equal(Call("value",App(Time,I("x"))),Call("shift",Call("expandedGraph",I("C")),Call("value",I("x")))),
            B("x",Union))),
            "unionShift has exactly the original one-step history shift as its underlying value. Signed base orbit membership is invariant under this operation: a base translate by t becomes the translate by t+1.",DescribeRole.Definition),
        Item("unionDeck","The original left deck action restricted to the union",Scope(Q(
            Equal(Call("value",Deck(I("a"),I("x"))),Call("groupHistory",I("C"),I("a"),Call("value",I("x")))),
            B("a",I("H")),B("x",Union))),
            "unionDeck a acts by the original groupHistory C a. It leaves the forgotten base path, including every edge number, unchanged. The group is arbitrary and can be infinite or noncommutative.",DescribeRole.Definition),
        Item("square_root_criterion","Complete square-root criterion",Scope(Imp(
            And(And(Call("Positive",I("d")),Call("Positive",I("e"))),And(
                And(Minimal(I("P"),I("d")),Minimal(I("Q"),I("e"))),
                Q(Seq(Translate(I("t"),I("P")),Sp,Neq,Sp,I("Q")),B("t",I("Int"))))),
            Iff(Ex(And(Q(Equal(App(I("R"),Deck(I("a"),I("x"))),Deck(I("a"),App(I("R"),I("x")))),
                B("a",I("H")),B("x",Union)),Equal(Call("iterate",I("R"),D(2)),Time)),
                B("R",Call("Map",Union,Union))),
                Or(And(Local(I("P"),I("d")),Local(I("Q"),I("e"))),And(Equal(I("d"),I("e")),
                    Ex(Equal(Mul(I("b"),Hol(I("Q"),I("e"))),Mul(Hol(I("P"),I("d")),I("b"))),B("b",I("H"))))))),
            B("d",I("Nat")),B("e",I("Nat"))),
            "Let d and e be the positive minimal periods of P and Q, and suppose no signed translate of P equals Q. Put h=orbitHolonomy C P d and k=orbitHolonomy C Q e. An arbitrary deck-equivariant endomap R of the entire original-history union has R squared equal to the original shift exactly in the displayed two cases. The preserving case requires both signed local equations: there are s:Fin d, m:Int and b:H with Commute b h, 2*s.val=1+d*m and b^2*h^m=1, and independently the same conditions for Q,e,k. The exchanging case requires d=e and an intertwiner b*k=h*b. Holonomy order or equality of ordinary periodic counts cannot replace the displayed holonomy condition. No time-commutation, bijectivity or component-preservation premise is imposed on R.",DescribeRole.Theorem),
        Paragraph(Text("For the reverse direction, the root equation first gives time commutation. Complete finite phase coordinates then show that the image tag of R is constant on each joint deck/time component. Applying the square equation to the two origins forces the tag map to be either the identity or the exchange. In the identity case the existing one-orbit root criterion gives the two local equations. In the exchange case each directed cross map carries the source seam into the target seam, giving d=e*m and e=d*n for integers m,n. Positivity forces d=e and m=n=1, so the first seam becomes b*k=h*b. This uses both directions of transport; equal infinite cardinalities would not determine the primitive periods.")),
        Paragraph(Text("For the converse exchange, complete atlas coordinates define F(point(t,z))=point(t,z*b) on the other component. Source equality at a signed seam m is respected because SemiconjBy.zpow_right directly gives b*k^m=h^m*b for every integer m. The inverse transport uses b inverse. Sending the first component through F and the second through time composed with F inverse squares to time on both. The complete charts are identified with the full original union by an equivalence whose underlying map is the same numbered-edge history; it intertwines original time and every original deck operation. Thus the construction neither omits histories nor adds artificial ones.")),
        Paragraph(Text("The argument combines classical permutation-centralizer component routing, regular-action right multiplication and ordered voltage-return holonomy. The one-orbit arithmetic is supplied by PrimitiveLiftRootCriterion; the signed power identity is supplied by pinned Mathlib SemiconjBy.zpow_right. This is a synthesis on actual history carriers and makes no claim of literature priority or global classification beyond these two signed base orbits."))
        )));
}
