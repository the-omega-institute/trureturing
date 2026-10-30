using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.PrimitiveLifts;

internal sealed class ReturnAtlasFiniteCoversDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/PrimitiveLifts/ReturnAtlasFiniteCovers.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Q(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. v], f);
    private static Formula Ex(Formula f, params Formula.BoundVariable[] v) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. v], f);
    private static Formula And(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Implies,Sp,Open,b,Close,Close);
    private static Formula Iff(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,F.Iff,Sp,Open,b,Close,Close);
    private static Formula Mul(Formula a, Formula b) => Call("mul",a,b);
    private static Formula Add(Formula a, Formula b) => Seq(Open,a,Plus,b,Close);
    private static Formula Sub(Formula a, Formula b) => Seq(Open,a,Minus,b,Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Inv(Formula a) => Call("inverse",a);
    private static Formula App(Formula f, Formula x) => Call("apply",f,x);
    private static Formula First(Formula p) => Call("first",p);
    private static Formula Second(Formula p) => Call("second",p);
    private static Formula Val(Formula p) => Call("val",p);
    private static Formula Cast(Formula p) => Call("intCast",p);
    private static Formula Period(Formula a) => Call("period",a);
    private static Formula Hol(Formula a) => Call("holonomy",a);
    private static Formula Point(Formula a, Formula t, Formula z) => Call("point",a,t,z);
    private static Formula Scope(Formula f, params Formula.BoundVariable[] rest) => Q(Seq(
        OpenBracket,Call("Group",I("H")),CloseBracket,Q(f,
        [B("X",I("Type")),B("Y",I("Type")),B("A",Call("ReturnAtlas",I("H"),I("X"))),
        B("B",Call("ReturnAtlas",I("H"),I("Y"))),..rest])),B("H",I("Type")));
    private static Formula DeckLaw => Q(Equal(
        App(I("f"),Call("deck",I("A"),I("a"),I("x"))),
        Call("deck",I("B"),I("a"),App(I("f"),I("x")))),B("a",I("H")),B("x",I("X")));
    private static Formula TimeLaw => Q(Equal(App(I("f"),Call("time",I("A"),I("x"))),
        Call("time",I("B"),App(I("f"),I("x")))),B("x",I("X")));
    private static Formula Seed => Equal(App(I("f"),Point(I("A"),D(0),D(1))),
        Point(I("B"),Cast(Val(I("r"))),I("b")));
    private static Formula Ratio(Formula m) => Equal(Period(I("A")),Mul(Period(I("B")),m));
    private static Formula Seam(Formula m, Formula b) => Equal(Mul(b,Pow(Hol(I("B")),Cast(m))),
        Mul(Hol(I("A")),b));
    private static Formula Law(Formula r, Formula b) => Q(Equal(
        App(I("f"),Point(I("A"),I("t"),I("z"))),
        Point(I("B"),Add(I("t"),Cast(Val(r))),Mul(I("z"),b))),B("t",I("Int")),B("z",I("H")));
    private static Formula DataType => Call("Prod",I("Nat"),Call("Prod",Call("Fin",Period(I("B"))),I("H")));
    private static Formula DataLaw(Formula p) => And(Call("Positive",First(p)),And(Ratio(First(p)),
        And(Seam(First(p),Second(Second(p))),Law(First(Second(p)),Second(Second(p))))));
    private static Formula Fiber => Seq(OpenBrace,I("x"),Colon,I("X"),Sp,Mid,Sp,
        Equal(App(I("f"),I("x")),I("y")),CloseBrace);
    private static Formula TargetCoordinate => Call("inverseCoordinates",I("B"),I("y"));
    private static Formula EnumerationAt(Formula s, Formula w) => Point(I("A"),
        Add(Sub(s,Cast(Val(I("r")))),
            Mul(Cast(Period(I("B"))),Cast(Val(I("j"))))),
        Mul(Mul(w,Pow(Hol(I("B")),Sub(D(0),Cast(Val(I("j")))))),Inv(I("b"))));
    private static Formula Enumeration => EnumerationAt(Cast(Val(First(TargetCoordinate))),Second(TargetCoordinate));
    private static Formula SignedFiber => Seq(OpenBrace,I("x"),Colon,I("X"),Sp,Mid,Sp,
        Equal(App(I("f"),I("x")),Point(I("B"),I("s"),I("w"))),CloseBrace);
    private static Formula SignedEnumeration => Call("fiberEnumeration",I("A"),I("B"),I("f"),I("m"),
        I("r"),I("b"),I("s"),I("w"));
    private static Formula.BoundVariable MapBinder => B("f",Call("Map",I("X"),I("Y")));
    private static Formula.BoundVariable PhaseBinder => B("r",Call("Fin",Period(I("B"))));
    private static DocumentBlock Item(string selector, string title, Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("return-atlas-cover-"+selector.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+selector),H(title),StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The primitive-base period ratio is the exact degree of an intertwining map, even for infinite noncommutative deck groups.",
        H("Finite covers of signed return atlases"),Blocks(
        Paragraph(Text("Let A and B be complete ReturnAtlas charts over the same arbitrary group H, with positive natural periods d and e and holonomies h and k. Their full signed equality laws are A(t,z)=A(s,w) exactly when t=s+d*n and z*h^n=w for an integer n, and similarly for B. Atlas periods describe the primitive base return; they need not be the ordinary minimal periods of the lifted time maps. Every statement here concerns sets and specified deck and time maps, with no topology, finiteness, commutativity or torsion assumption on H.")),
        Item("normal_form","Unique degree and normalized seed",Scope(Imp(And(DeckLaw,TimeLaw),
            Ex(And(DataLaw(I("p")),Q(Imp(DataLaw(I("q")),Equal(I("q"),I("p"))),B("q",DataType))),
                B("p",DataType))),MapBinder),
            "For every f:X->Y intertwining all left deck maps and the specified time maps, there is exactly one triple (m,(r,b)) with m a positive natural, r:Fin e and b:H such that d=e*m, b*k^m=h*b, and f(A(t,z))=B(t+r.val,z*b) for all signed t and all z. The pair (r,b) is exactly the complete normalized coordinate of f(A(0,1)). The period ratio follows from the existing seam obstruction; comparing the seam again at this actual seed gives its own holonomy equation. Reducing a signed source point to complete phase coordinates and transporting holonomy powers then extends the forward law to every negative representative as well. Positivity of e makes m unique, and uniqueness of complete target coordinates makes (r,b) unique.",DescribeRole.Theorem),
        Item("coveringMap","Transport with the target phase",Scope(Q(Equal(
            Call("coveringMap",I("A"),I("B"),I("r"),I("b"),I("x")),
            App(Call("iterate",Call("time",I("B")),Val(I("r"))),
                Call("transport",I("A"),I("B"),I("b"),I("x")))),PhaseBinder,B("b",I("H")),B("x",I("X")))),
            "coveringMap A B r b first applies the existing complete-coordinate transport and then advances target time by r.val. Under d=e*m and b*k^m=h*b it sends every A(t,z) to B(t+r.val,z*b), including signed t. Indeed b*k^(m*n)=h^n*b is supplied by SemiconjBy.zpow_right and zpow_mul; this is precisely what makes each source seam respected in the target, without requiring d=e.",DescribeRole.Definition),
        Item("map_criterion","Exact existence with a prescribed seed",Scope(Iff(
            Ex(And(DeckLaw,And(TimeLaw,Seed)),MapBinder),
            Ex(And(Call("Positive",I("m")),And(Ratio(I("m")),Seam(I("m"),I("b")))),B("m",I("Nat")))),
            PhaseBinder,B("b",I("H"))),
            "For each prescribed r:Fin e and b:H, there exists a deck and time intertwiner f with f(A(0,1))=B(r.val,b) if and only if a positive natural m satisfies d=e*m and b*k^m=h*b. Necessity identifies the unique normalized seed in normal_form with the prescribed one. Sufficiency is the actual coveringMap A B r b on the full source carrier. Thus unequal-period maps exist exactly when the target holonomy raised to the period ratio is conjugate to the source holonomy in the displayed order.",DescribeRole.Theorem),
        Item("fiberEnumeration","The signed fiber map",Scope(Imp(Law(I("r"),I("b")),And(
            Seq(App(SignedEnumeration,I("j")),Colon,SignedFiber),
            Equal(Val(App(SignedEnumeration,I("j"))),EnumerationAt(I("s"),I("w"))))),
            MapBinder,B("m",I("Nat")),PhaseBinder,B("b",I("H")),B("s",I("Int")),B("w",I("H")),
            B("j",Call("Fin",I("m")))),
            "For any signed target representative B(s,w), fiberEnumeration sends j:Fin m to A(s-r.val+e*j.val,w*k^(-(j.val:Int))*b^(-1)), together with a proof that its image under f is B(s,w). This membership uses only the signed normal law: the target seam j cancels the negative power. The application suppresses the proof of that law. The degree ratio and source holonomy constraint enter when proving that this map is bijective.",DescribeRole.Definition),
        Item("fiberEnumeration_bijective","Signed reconstruction is injective and exhaustive",Scope(Imp(
            And(Ratio(I("m")),And(Seam(I("m"),I("b")),Law(I("r"),I("b")))),
            Call("Bijective",SignedEnumeration)),MapBinder,B("m",I("Nat")),PhaseBinder,B("b",I("H")),
            B("s",I("Int")),B("w",I("H"))),
            "Under d=e*m, b*k^m=h*b and the full signed normal law, the displayed fiberEnumeration is bijective for every integer s and every w:H. Injectivity uses the source seam and the Fin m bounds. Surjectivity reconstructs every source point from the residue of its target seam modulo m, using the signed power relation in its original noncommutative order. Thus every signed target representation enumerates the entire same fiber, not a chosen subfamily.",DescribeRole.Theorem),
        Item("fiberEquiv","Every point of every fiber, exactly once",Scope(Imp(
            And(Ratio(I("m")),And(Seam(I("m"),I("b")),Law(I("r"),I("b")))),And(
            Seq(Call("fiberEquiv",I("A"),I("B"),I("f"),I("m"),I("r"),I("b"),I("y")),Colon,
                Call("Equiv",Call("Fin",I("m")),Fiber)),
            Q(Equal(Val(App(Call("fiberEquiv",I("A"),I("B"),I("f"),I("m"),I("r"),I("b"),I("y")),I("j"))),
                Enumeration),B("j",Call("Fin",I("m")))))),MapBinder,B("m",I("Nat")),PhaseBinder,
            B("b",I("H")),B("y",I("Y"))),
            "Given the degree, seed and signed law furnished by normal_form, fiberEquiv is an actual equivalence Fin m -> {x:X // f(x)=y} for every y:Y. Write (s,w)=B.coordinates.symm(y), where s:Fin e, so y=B(s.val,w). Its forward value at j is A(s.val-r.val+e*j.val, w*k^(-(j.val:Int))*b^(-1)). The displayed application suppresses only the proofs of the ratio, seam and signed law. The inverse is obtained from the proved bijectivity of this explicit enumeration, not from a cardinal equation. Positivity of m follows from d=e*m and positivity of the atlas periods.",DescribeRole.Definition),
        Paragraph(Text("The same enumeration works over any signed representative y=B(s,w): E(j)=A(s-r.val+e*j.val,w*k^(-(j.val:Int))*b^(-1)). Membership is the target seam j. If E(j)=E(l), the source return law forces j.val-l.val=m*q. The strict Fin m bounds force q=0 and j=l. Conversely, write an arbitrary preimage as A(t,z). Its image equality gives t+r.val=s+e*n and (z*b)*k^n=w for an arbitrary integer n. Euclidean division gives n=j.val+m*q even when n is negative. The source seam q and b*k^(m*q)=h^q*b then show that this original preimage is E(j). The order of w, the negative holonomy power and b inverse is essential.")),
        Paragraph(Text("The joint deck and signed time operations give a transitive H times Z action on each atlas carrier. At the normalized seed, the cyclic return stabilizer generated by the source seam maps into the target return stabilizer by multiplication of its integer parameter by m. Its index is m; the explicit enumeration realizes the corresponding m classes as a full fiber. This links arithmetic divisibility of primitive-base periods to an exact finite-fiber structure without counting the group or the ambient carriers.")),
        Paragraph(Text("For a root that routes a cycle of joint components, applying these positive degree ratios around the cycle makes their product one. Each ratio is therefore one, so each routed map has singleton fibers and is a bijection, and the component holonomies obey the degree-one conjugacy condition. This explains the equal-period transport used in the two-orbit square-root and three-orbit cube-root criteria. It is an interpretation of cyclic stabilizer inclusion and the proved fiber construction, with no claim of literature priority."))
        )));
}
