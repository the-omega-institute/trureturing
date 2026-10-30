using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class PrimeOrbitRootCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimeOrbitRootCriterion.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. v], f);
    private static Formula And(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula Or(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Lor,Sp,Open,b,Close,Close);
    private static Formula Iff(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,F.Iff,Sp,Open,b,Close,Close);
    private static Formula Mul(Formula a, Formula b) => Call("mul",a,b);
    private static Formula Add(Formula a, Formula b) => Seq(Open,a,Plus,b,Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
    private static Formula FinP => Call("Fin",I("p"));
    private static Formula Ai(Formula i) => App(I("A"),i);
    private static Formula Period(Formula a) => Call("period",a);
    private static Formula Hol(Formula a) => Call("holonomy",a);
    private static Formula Carrier => Call("Sigma",I("X"));
    private static Formula Time => Call("jointTime",I("A"));
    private static Formula Deck(Formula a) => Call("jointDeck",I("A"),a);
    private static Formula Cast(Formula x) => Call("intCast",x);
    private static Formula Scope(Formula f) => Q(Seq(OpenBracket,Call("Group",I("H")),CloseBracket,
        Q(f,B("p",I("Nat")),B("X",Call("Map",FinP,I("Type"))),
            B("A",Call("DependentReturnAtlases",I("H"),I("X"))))),B("H",I("Type")));
    private static Formula FamilyScope(Formula f) => Q(Seq(OpenBracket,Call("Group",I("H")),CloseBracket,
        Q(f,B("J",I("Type")),B("X",Call("Map",I("J"),I("Type"))),
            B("A",Call("DependentReturnAtlases",I("H"),I("X"))))),B("H",I("Type")));
    private static Formula LocalEquation(Formula a) => Ex(And(Call("Commute",I("b"),Hol(a)),And(
        Equal(Mul(Cast(I("p")),Cast(Call("val",I("s")))),Add(D(1),Mul(Cast(Period(a)),I("m")))),
        Equal(Mul(Pow(I("b"),I("p")),Pow(Hol(a),I("m"))),D(1)))),
        B("s",Call("Fin",Period(a))),B("m",I("Int")),B("b",I("H")));
    private static Formula Pairwise => Q(And(Equal(Period(Ai(I("i"))),Period(Ai(I("j")))),
        Ex(Equal(Mul(I("b"),Hol(Ai(I("j")))),Mul(Hol(Ai(I("i"))),I("b"))),B("b",I("H")))),
        B("i",FinP),B("j",FinP));
    private static Formula Root => Ex(And(Q(Equal(App(I("R"),App(Deck(I("a")),I("q"))),
        App(Deck(I("a")),App(I("R"),I("q")))),B("a",I("H")),B("q",Carrier)),
        Equal(Call("iterate",I("R"),I("p")),Time)),B("R",Call("Map",Carrier,Carrier)));
    private static DocumentBlock Item(string selector, string title, Formula formula, string text,
        DescribeRole role) => Describe.Lean(DescribeId.Create("prime-orbit-"+selector.Replace("_","-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix+selector),H(title),StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime cardinality turns component routing into an exact local-or-cyclic root criterion.",
        H("Prime roots on complete return-chart families"),Blocks(
        Paragraph(Text("Let p be any prime natural number, H any group, X:Fin p->Type an arbitrary dependent family, and A_i:ReturnAtlas H (X i) complete signed return charts. Write d_i>0 for their atlas periods and h_i for their holonomies. DependentReturnAtlases(H,X) denotes precisely this dependent family of charts, and Sigma(X) is the entire disjoint carrier of pairs (i,x) with x:X i. The chart equality is A_i(t,z)=A_i(s,w) exactly when t=s+d_i*m and z*h_i^m=w for some integer m. The group may be infinite and noncommutative. The d_i are primitive-base return periods, not ordinary minimal periods of the lifted time maps.")),
        Item("jointTime","Time on the dependent union",FamilyScope(Q(Equal(App(Time,I("q")),
            Call("pair",Call("first",I("q")),Call("time",Ai(Call("first",I("q"))),Call("second",I("q"))))),
            B("q",Carrier))),
            "For an arbitrary index type J and a family A_j, the time map T sends (i,x) to (i,A_i.time(x)). Every point of every chart remains in the carrier.",DescribeRole.Definition),
        Item("jointDeck","Left deck action on the dependent union",FamilyScope(Q(Equal(App(Deck(I("a")),I("q")),
            Call("pair",Call("first",I("q")),Call("deck",Ai(Call("first",I("q"))),I("a"),Call("second",I("q"))))),
            B("a",I("H")),B("q",Carrier))),
            "For an arbitrary index type J and a:H the deck map D_a sends (i,x) to (i,A_i.deck(a,x)). It uses the same left group element in each component; signed return holonomy still multiplies on the right.",DescribeRole.Definition),
        Item("Local","The full signed local equation",Q(Seq(OpenBracket,Call("Group",I("H")),CloseBracket,
            Q(Equal(Call("Local",I("p"),I("B")),LocalEquation(I("B"))),
                B("p",I("Nat")),B("Y",I("Type")),B("B",Call("ReturnAtlas",I("H"),I("Y"))))),B("H",I("Type"))),
            "Local p B means that s:Fin B.period, m:Int and b:H satisfy b*B.holonomy=B.holonomy*b, p*s.val=1+B.period*m and b^p*B.holonomy^m=1. The integer m can be negative. This is the existing exact ReturnAtlas.root_criterion equation, with no ordinary-time-period replacement.",DescribeRole.Definition),
        Item("prime_root_criterion","Exact prime-family root criterion",Scope(Seq(
            Call("Prime",I("p")),Sp,Implies,Sp,Iff(Root,
                Or(Q(LocalEquation(Ai(I("i"))),B("i",FinP)),Pairwise)))),
            "There exists a map R:Sigma X->Sigma X with R(D_a(q))=D_a(R(q)) for every a and q, and R iterated p times equal to T, if and only if either every A_i satisfies Local p A_i or for every i,j one has d_i=d_j and some b:H with b*h_j=h_i*b. The two alternatives may overlap. R is not assumed to preserve charts, be bijective, or commute with time.",DescribeRole.Theorem),
        Paragraph(Text("Necessity first derives time commutation from R^p=T and injectivity from the injectivity of T. Completeness of each chart makes the target component of R(i,x) independent of x: deck moves cover its group coordinate, and nonnegative time moves cover its normalized finite phase. This induces sigma:Fin p->Fin p with sigma^p=id. Each restricted map between routed components is injective and intertwines deck and time. Apply ReturnAtlasFiniteCovers.normal_form and its actual fiberEquiv: a positive degree m gives Fin m equivalent to the full preimage of every target point. Injectivity forces any two such preimages equal; if m>1 the images of 0 and 1 contradict injectivity of that equivalence. Hence m=1, yielding equal atlas periods and b*h_j=h_i*b without counting H.")),
        Paragraph(Text("If sigma fixes every index, restriction gives an actual pth root in each chart, and the existing local root criterion gives all local equations. Otherwise choose a nonfixed index o. Mathlib's prime minimal-period theorem gives minimalPeriod(sigma,o)=p. Its p distinct iterates exhaust Fin p. Apply the same injective-factor argument to every iterate of R to identify A_o with every chart. Inverting and composing the resulting conjugacies gives the displayed condition for every ordered pair i,j. No fixed-order enumeration is used.")),
        Paragraph(Text("For sufficiency, local roots combine directly on the dependent union. In the other case choose gauges b_i with b_i*h_i=h_o*b_i and equal periods. Existing complete-coordinate transport identifies the entire union with Fin p times X_o, by (i,x)->(i,transport(A_i,A_o,b_i inverse,x)). In these coordinates define C(i,y)=((i.val+1) mod p, T_o^floor((i.val+1)/p)(y)). Induction proves C^n(i,y)=((i.val+n) mod p, T_o^floor((i.val+n)/p)(y)). Thus C^p(i,y)=(i,T_o(y)); exactly one time step occurs at the wrap. Deck commutation of T_o makes C deck equivariant. Conjugating C back through the full chart equivalence constructs the required actual map R.")),
        Paragraph(Text("This connects cyclic permutation arithmetic, the signed finite-cover degree, and nonabelian holonomy conjugacy. The restriction to exactly p charts makes a single nonfixed prime orbit fill the entire index set. Larger finite families require additional orbit multiplicity information; no criterion for those families is asserted here. These arguments combine established permutation and return-chart mechanisms, with no claim of literature priority."))
        )));
}
