using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class ThreeOrbitCubeRootCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCriterion.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll,[..v],f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[..v],f);
    private static Formula And(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula Or(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Lor,Sp,Open,b,Close,Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Implies,Sp,Open,b,Close,Close);
    private static Formula Iff(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,F.Iff,Sp,Open,b,Close,Close);
    private static Formula Mul(Formula a, Formula b) => Call("mul",a,b);
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
    private static Formula Hist => Call("History",Call("expandedGraph",I("C")));
    private static Formula Union => Call("OrbitUnion",I("C"),I("P"),I("Q"),I("S"));
    private static Formula Time => Call("unionShift",I("C"),I("P"),I("Q"),I("S"));
    private static Formula Deck(Formula a, Formula x) => Call("unionDeck",I("C"),I("P"),I("Q"),I("S"),a,x);
    private static Formula Translate(Formula t, Formula p) => Call("translate",Call("baseGraph",I("C")),t,p);
    private static Formula Orbit(Formula p) => Ex(Equal(Call("forgetHistory",I("x")),Translate(I("t"),p)),B("t",I("Int")));
    private static Formula Hol(Formula p, Formula d) => Call("orbitHolonomy",I("C"),p,d);
    private static Formula Local(Formula p, Formula d) => Ex(And(Call("Commute",I("b"),Hol(p,d)),And(
        Equal(Mul(D(3),Call("intCast",Call("val",I("s")))),Seq(D(1),Plus,Mul(Call("intCast",d),I("m")))),
        Equal(Mul(new Formula.Power(I("b"),D(3)),new Formula.Power(Hol(p,d),I("m"))),D(1)))),
        B("s",Call("Fin",d)),B("m",I("Int")),B("b",I("H")));
    private static Formula Intertwiner(Formula p, Formula d, Formula q, Formula e) => Ex(
        Equal(Mul(I("b"),Hol(q,e)),Mul(Hol(p,d),I("b"))),B("b",I("H")));
    private static Formula Minimal(Formula p, Formula d) => Equal(Call("minimalPeriod",Call("baseShift",I("C")),p),d);
    private static Formula Disjoint(Formula p, Formula q) => Q(Seq(Translate(I("t"),p),Sp,Neq,Sp,q),B("t",I("Int")));
    private static Formula Scope(Formula f, params Formula.BoundVariable[] rest) => Q(Seq(
        OpenBracket,Call("Group",I("H")),CloseBracket,Q(f,[B("n",I("Nat")),
        B("C",Call("GroupMat",I("H"),I("n"),I("n"))),B("P",Call("Path",I("C"))),
        B("Q",Call("Path",I("C"))),B("S",Call("Path",I("C"))),..rest])),B("H",I("Type")));
    private static DocumentBlock Item(string s,string title,Formula f,string text,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("three-orbit-"+s.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+s),H(title),StatementSource.FromAuthor(Disp(f)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original histories over three disjoint primitive base orbits admit precisely local cube roots or a compatible three-cycle.",
        H("Equivariant cube roots on three primitive lift orbits"),Blocks(
        Item("OrbitUnion","All original histories over the three signed base orbits",Scope(Equal(Union,
            Seq(OpenBrace,I("x"),Colon,Hist,Sp,Mid,Sp,Or(Orbit(I("P")),Or(Orbit(I("Q")),Orbit(I("S")))),CloseBrace))),
            "OrbitUnion C P Q S contains every original bilateral legal history of expandedGraph C whose forgotten numbered-edge history is an integer translate of P, Q or S. All phases and group coordinates remain present.",DescribeRole.Definition),
        Item("unionShift","The restricted original time shift",Scope(Q(
            Equal(Call("value",App(Time,I("x"))),Call("shift",Call("expandedGraph",I("C")),Call("value",I("x")))),B("x",Union))),
            "The time map is exactly the original one-step shift on each underlying history. An integer base phase t becomes t+1.",DescribeRole.Definition),
        Item("unionDeck","The original deck action on the full union",Scope(Q(
            Equal(Call("value",Deck(I("a"),I("x"))),Call("groupHistory",I("C"),I("a"),Call("value",I("x")))),B("a",I("H")),B("x",Union))),
            "The left action of a is the original groupHistory C a. It preserves the forgotten numbered-edge history. No finiteness or commutativity assumption is imposed on H.",DescribeRole.Definition),
        Item("cube_root_criterion","Complete three-orbit cube-root criterion",Scope(Imp(
            And(And(Call("Positive",I("d")),And(Call("Positive",I("e")),Call("Positive",I("f")))),
                And(And(Minimal(I("P"),I("d")),And(Minimal(I("Q"),I("e")),Minimal(I("S"),I("f")))),
                    And(Disjoint(I("P"),I("Q")),And(Disjoint(I("P"),I("S")),Disjoint(I("Q"),I("S")))))),
            Iff(Ex(And(Q(Equal(App(I("R"),Deck(I("a"),I("x"))),Deck(I("a"),App(I("R"),I("x")))),
                B("a",I("H")),B("x",Union)),Equal(Call("iterate",I("R"),D(3)),Time)),B("R",Call("Map",Union,Union))),
                Or(And(Local(I("P"),I("d")),And(Local(I("Q"),I("e")),Local(I("S"),I("f")))),
                    And(Equal(I("d"),I("e")),And(Equal(I("e"),I("f")),
                        And(Intertwiner(I("P"),I("d"),I("Q"),I("e")),Intertwiner(I("Q"),I("e"),I("S"),I("f")))))))),
            B("d",I("Nat")),B("e",I("Nat")),B("f",I("Nat"))),
            "Let d,e,f be the positive minimal periods of P,Q,S, whose signed base orbits are pairwise disjoint. A deck-equivariant endomap R of the entire original-history union cubes to the original shift exactly when the three local signed cube-root equations all hold, or d=e=f and consecutive ordered holonomies admit intertwiners b*hQ=hP*b and c*hS=hQ*c. Each local equation has s:Fin d, m:Int and b:H with Commute b h, 3*s.val=1+d*m and b^3*h^m=1, and independently for the other components. No preservation of components, time commutation or bijectivity is assumed of R.",DescribeRole.Theorem),
        Paragraph(Text("The three signed base-orbit hypotheses identify the disjoint union of the complete actual lift atlases with this full history subtype. The equivalence keeps the very same underlying numbered-edge history, intertwines every original deck operation and intertwines the original time shift. Conjugating an arbitrary root through it gives precisely the three-chart cube-root problem, rather than a root on selected representatives or a reduced fibre.")),
        Paragraph(Text("The atlas criterion extracts the induced action on three components. A cube root either preserves them all or permutes them in a three-cycle. In the latter case cyclic seam divisibility forces the three primitive periods to be equal, and the ordered seam equations force the displayed conjugacies. Compatible transports then construct a root with one time step on the closing arrow. The order in these group equations is retained; equal holonomy orders or equal ordinary periodic counts are insufficient substitutes. The result concerns these three signed base orbits and does not claim a classification for an arbitrary number of components or literature priority."))
        )));
}
