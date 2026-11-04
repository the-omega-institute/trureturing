using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class ThreeOrbitCubeRootChartsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ThreeOrbitCubeRootCharts.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll,[..v],f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[..v],f);
    private static Formula And(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula Or(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Lor,Sp,Open,b,Close,Close);
    private static Formula Iff(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,F.Iff,Sp,Open,b,Close,Close);
    private static Formula Mul(Formula a, Formula b) => Call("mul",a,b);
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
    private static Formula Period(Formula a) => Call("period",a);
    private static Formula Hol(Formula a) => Call("holonomy",a);
    private static Formula Carrier => Call("Sum",I("X"),Call("Sum",I("Y"),I("Z")));
    private static Formula Time => Call("jointTime",I("A"),I("B"),I("C"));
    private static Formula Deck(Formula a, Formula x) => Call("jointDeck",I("A"),I("B"),I("C"),a,x);
    private static Formula Local(Formula a) => Ex(And(Call("Commute",I("b"),Hol(a)),And(
        Equal(Mul(D(3),Call("intCast",Call("val",I("s")))),Seq(D(1),Plus,Mul(Call("intCast",Period(a)),I("m")))),
        Equal(Mul(new Formula.Power(I("b"),D(3)),new Formula.Power(Hol(a),I("m"))),D(1)))),
        B("s",Call("Fin",Period(a))),B("m",I("Int")),B("b",I("H")));
    private static Formula Intertwiner(Formula a, Formula b) => Ex(
        Equal(Mul(I("b"),Hol(b)),Mul(Hol(a),I("b"))),B("b",I("H")));
    private static Formula Scope(Formula f) => Q(Seq(OpenBracket,Call("Group",I("H")),CloseBracket,Q(f,
        B("X",I("Type")),B("Y",I("Type")),B("Z",I("Type")),
        B("A",Call("ReturnAtlas",I("H"),I("X"))),B("B",Call("ReturnAtlas",I("H"),I("Y"))),
        B("C",Call("ReturnAtlas",I("H"),I("Z"))))),B("H",I("Type")));
    private static DocumentBlock Item(string s,string title,Formula f,string text,DescribeRole role) =>
        Describe.Lean(DescribeId.Create("three-chart-"+s.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+s),H(title),StatementSource.FromAuthor(Disp(f)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three complete return charts admit an equivariant cube root exactly by local roots or a compatible component cycle.",
        H("Cube roots on three signed return charts"),Blocks(
        Item("jointTime","Time on the three-chart carrier",Scope(Equal(Time,
            Call("sumMap",Call("time",I("A")),Call("sumMap",Call("time",I("B")),Call("time",I("C")))))),
            "The carrier is X plus (Y plus Z), with no identification across components. jointTime applies each chart's specified time map to its own component.",DescribeRole.Definition),
        Item("jointDeck","The joint left deck action",Scope(Q(Equal(Deck(I("a"),I("x")),
            App(Call("sumMap",Call("deck",I("A"),I("a")),Call("sumMap",Call("deck",I("B"),I("a")),Call("deck",I("C"),I("a")))),I("x"))),
            B("a",I("H")),B("x",Carrier))),
            "Each group element acts by the given left deck map on every chart. The group may be infinite or noncommutative.",DescribeRole.Definition),
        Item("Local","The signed one-chart cube-root equation",Q(Seq(OpenBracket,Call("Group",I("H")),CloseBracket,Q(
            Iff(Call("Local",I("A")),Local(I("A"))),B("X",I("Type")),B("A",Call("ReturnAtlas",I("H"),I("X"))))),B("H",I("Type"))),
            "Local A means that some finite phase s, signed return exponent m and group element b satisfy Commute b h, 3*s.val=1+d*m and b^3*h^m=1, where d=A.period and h=A.holonomy. The return exponent can be negative.",DescribeRole.Definition),
        Item("chart_criterion","Complete equivariant cube-root criterion",Scope(Iff(
            Ex(And(Q(Equal(App(I("r"),Deck(I("a"),I("x"))),Deck(I("a"),App(I("r"),I("x")))),
                B("a",I("H")),B("x",Carrier)),Equal(Call("iterate",I("r"),D(3)),Time)),B("r",Call("Map",Carrier,Carrier))),
            Or(And(Local(I("A")),And(Local(I("B")),Local(I("C")))),
                And(Equal(Period(I("A")),Period(I("B"))),And(Equal(Period(I("B")),Period(I("C"))),
                    And(Intertwiner(I("A"),I("B")),Intertwiner(I("B"),I("C")))))))),
            "A deck-equivariant endomap has cube equal to jointTime precisely when each chart satisfies its local signed equation, or all three periods agree and consecutive holonomies admit the displayed intertwiners. The root is not assumed to commute with time, to be bijective or to preserve components. A return atlas already includes a positive period and a complete equality law.",DescribeRole.Theorem),
        Paragraph(Text("The root equation implies time commutation. Finite phase coordinates and deck equivariance force the target component to be constant on each source component. The resulting map of three labels has cube equal to the identity, so it is the identity or one of the two three-cycles. In a three-cycle, the three directed seam equations give cyclic divisibility of the positive periods. All divisibility multipliers must therefore equal one, and the seam equations become holonomy intertwiners.")),
        Paragraph(Text("Conversely, local roots act separately. For compatible holonomies, transport in signed coordinates sends point(t,z) to point(t,z*b) on the next chart. Two successive transports use b and c. The return arrow uses (b*c) inverse and then one time step. The resulting map cubes to time on every component; the order of the factors is essential for a noncommutative group. This is a structural consequence of complete return charts and classical permutation component routing, without a claim of literature priority."))
        )));
}
