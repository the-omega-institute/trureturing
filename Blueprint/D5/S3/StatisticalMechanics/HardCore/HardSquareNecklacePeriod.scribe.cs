using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class HardSquareNecklacePeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/HardCore/HardSquareNecklacePeriod.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/adamaszek2012hardsquares");
    private const string NecklaceQuote = "\"We define a (k, n)-necklace. It is a collection of 2k points (stones) distributed along the circumference of a circle of length n, together with an assignment of a number from {−2, −1, 1, 2} to each of the stones.\" (p. 12).";
    private const string ClaimQuote = "\"The length of every cycle in the graph Neck(k, n) divides n−3k. In other words, for every (k, n)-necklace N we have Tⁿ⁻³ᵏN = N.\" (Conjecture 7.4, p. 14).";
    private const string PairQuote = "\"consecutive stones face in opposite directions,\" (p. 12); \"if two consecutive stones face away from each other then their distance is an odd integer,\" \"if two consecutive stones face towards each other then their distance plus the lengths of their vectors is an odd integer,\" and \"if two consecutive stones face towards each other then their distance is at least 3; moreover if their distance is exactly 3 then their vectors have length 1.\" (p. 13).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adamaszek's necklace transformation combines simultaneous jumps, vector changes, and corrections at facing gaps of length three. Every legal necklace on an even circle returns to its isometry class after n−3k steps. Compressing a lifted stone at x with index i and signed vector v to y=2x+v−3i turns collisions into exchanges of unit velocities. After half the compressed circumference, both velocity classes have shifted equally; winding and parity recover the physical vectors and positions.",
        H("The period of hard-square necklaces"),
        Blocks(
            Node("vectors", "Stone vectors", Disp(Eq(Named("Vec"), Set(NegTwo(), NegOne(), PosOne(), PosTwo()))),
                NecklaceQuote + " The four constructors encode the four signed vectors in the stated order.", "Vec"),
            Constructor("negtwo", "Vector −2", "Vec.negTwo", NegTwo()),
            Constructor("negone", "Vector −1", "Vec.negOne", NegOne()),
            Constructor("posone", "Vector 1", "Vec.posOne", PosOne()),
            Constructor("postwo", "Vector 2", "Vec.posTwo", PosTwo()),
            Node("value", "Signed displacement", VectorTable("value", Signed(-2), Signed(-1), D(1), D(2)),
                "\"The vector points 1 or 2 units clockwise (positive value) or anti-clockwise (negative value) from each stone and we say a stone faces the direction of its vector.\" (p. 12). value is the signed integer displacement.", "Vec.value"),
            Node("length", "Vector length", VectorTable("length", D(2), D(1), D(1), D(2)),
                "The length is the absolute value of the signed vector, either one or two.", "Vec.length"),
            Node("positive", "Clockwise direction", PositiveFormula(),
                "A vector is positive exactly for the two clockwise constructors posOne and posTwo.", "Vec.positive"),
            Node("turn", "TURN", VectorTable("turn", PosOne(), PosTwo(), NegTwo(), NegOne()),
                "\"(TURN) all stone vectors change according to the rule −2→1, −1→2, 1→−2, 2→−1,\" (p. 13). Both the direction and the length switch to the other option.", "Vec.turn"),
            Node("negate", "Reflection of a vector", VectorTable("negate", PosTwo(), PosOne(), NegOne(), NegTwo()),
                "A reflection reverses the tangent direction and preserves the vector length.", "Vec.negate"),
            Node("shorten", "Length correction", VectorTable("shorten", NegOne(), NegOne(), PosOne(), PosOne()),
                "\"(FIX) if any two stones find themselves in distance 3 facing each other and any of their vectors has length 2, then adjust the offending vectors by reducing their length to 1.\" (p. 13). shorten preserves direction and reduces length two to one, leaving length one unchanged.", "Vec.shorten"),
            Node("config", "Configurations on the integer circle", ConfigFormula(),
                NecklaceQuote + " Each site of ZMod n carries either no stone or one of the four vectors. The pair conditions force every consecutive distance to be integral, so rotation of the origin places all stones at integer sites.", "Config"),
            Node("stone", "Occupied sites", StoneFormula(),
                "A site is occupied exactly when its optional vector is some v for a stone vector v.", "HasStone"),
            Node("distance", "Clockwise distance", DistanceFormula(),
                "val denotes ZMod.val: the representative in {0,…,n−1} when n is positive. The clockwise distance is val(q−p). The formula uses a natural-valued distance, not a real fraction.", "clockwiseDistance"),
            Node("consecutive", "Cyclically consecutive stones", ConsecutiveFormula(),
                "Two distinct occupied sites are consecutive when the open clockwise arc between them is empty. This also includes the pair crossing the chosen origin.", "Consecutive"),
            Node("pair", "The four pair conditions", PairFormula(),
                PairQuote + " ofNat denotes Int.ofNat, the canonical coercion from naturals to integers. d is the positive clockwise gap in integers, v the left vector, and w the right vector. Left negative and right positive means facing away; left positive and right negative means facing towards.", "PairAdmissible"),
            Node("necklace", "Legal necklaces", NecklaceFormula(),
                NecklaceQuote + " \"We identify (k, n)-necklaces which differ by an isometry of the circle.\" (p. 13). IsNecklace includes positivity of n, exactly 2k occupied sites, and all four conditions for every cyclically consecutive pair. The global even-n and positive-k conventions occur in claim.", "IsNecklace"),
            Node("jump", "Simultaneous JUMP and TURN", JumpFormula(),
                "\"(JUMP) all stones jump as dictated by their vectors,\" (p. 13). cast denotes Int.cast, with its target ZMod n displayed explicitly. For the existential E displayed below, choose(E) means its chosen witness; fst and snd are its position and vector. A destination with an incoming stone receives its turned vector. On legal necklaces the inflow is unique; choice totalizes the function on illegal configurations.", "jumpTurn"),
            Node("fix", "Simultaneous FIX", FixFormula(),
                "\"(FIX) if any two stones find themselves in distance 3 facing each other and any of their vectors has length 2, then adjust the offending vectors by reducing their length to 1.\" (p. 13). All tests read the same post-JUMP, post-TURN configuration. ite(P,a,b) means a when P holds and b otherwise. A clockwise vector tests p+3 for a negative vector; an anticlockwise vector tests p−3 for a positive vector. Length-one vectors are unaffected by shorten.", "fix"),
            Node("transformation", "The necklace transformation", TransformationFormula(),
                "\"Next we describe a necklace transformation T which takes a (k, n)-necklace and performs the following operations:\" (p. 13). necklaceT applies JUMP and TURN simultaneously, followed by FIX.", "necklaceT"),
            Node("action", "Action on configurations", ActionFormula(),
                "Mathlib DihedralGroup n supplies rotations r(c) and reflections sr(c), whose forward point maps are q↦q+c and q↦−q+c. The action pulls a configuration back through the inverse point isometry; reflection also negates its vector. Option.map leaves none unchanged and applies negate to a present vector.", "circleIsometryAct"),
            Node("smul", "The isometry action instance", SmulFormula(),
                "The explicitly named SMul instance has smul equal to circleIsometryAct. Multiplication g•N in claim uses this instance.", "circleIsometrySMul"),
            Node("claim", "Conjecture 7.4", ClaimFormula(),
                ClaimQuote + " n is an even positive circle length and k≥1 counts half the stones. Config n, IsNecklace k N, and the rotation/reflection action encode the source's objects and identification. The exponent is natural subtraction n−3k; the proof derives 4k≤n from the pair conditions. iterate denotes Function.iterate; iterate(T,0) is the identity function.", "claim"),
            Describe.Lean(DescribeId.Create("adam-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Proof of Conjecture 7.4"), StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Sort the physical stones and extend their coordinates periodically to integers. The compressed positions yᵢ=2xᵢ+vᵢ−3i are strictly ordered, with circumference 2(n−3k); their velocities are sign(vᵢ)(2|vᵢ|−3), hence ±1. FIX exchanges the velocities at disjoint crossing pairs, so the compressed evolution is free motion followed by relabelling. At L=n−3k steps both velocities give the same spatial displacement modulo 2L, and an increasing bijection of the integer labels is a translation. The total compressed first moment determines this label shift as minus the number of negative compressed velocities. Even physical circumference fixes its parity, allowing recovery of each physical vector and position. The final isometry is a rotation, so reflection is not needed for the return."))),
                DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose, string declaration) =>
        Describe.Lean(DescribeId.Create("adam-" + id), DeclarationHandle.Create(Prefix + declaration[(declaration.LastIndexOf('.') + 1)..]),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Constructor(string id, string title, string declaration, Formula value) =>
        Node(id, title, Disp(Member(value, Named("Vec"))), "This constructor is the indicated signed stone vector.", declaration);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Zmod(Formula n) => Call("ZMod", n);
    private static Formula Conf(Formula n) => Call("Config", n);
    private static Formula Signed(int x) => x < 0 ? Seq(Minus, D((byte)-x)) : D((byte)x);
    private static Formula NegTwo() => Named("negTwo");
    private static Formula NegOne() => Named("negOne");
    private static Formula PosOne() => Named("posOne");
    private static Formula PosTwo() => Named("posTwo");
    private static Formula Set(params Formula[] xs) => new Formula.SetLiteral([.. xs]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual,b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan,b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Or,Parenthesized(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Not(Formula a) => Seq(Neg,Sp,Parenthesized(a));
    private static Formula All(string x, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(x),type,body);
    private static Formula Ex(string x, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(x),type,body);
    private static Formula Some(Formula x) => Call("some",x);
    private static Formula None() => Named("none");
    private static Formula Positive(Formula x) => Call("positive",x);
    private static Formula At(Formula n,Formula p,Formula q) => Call("clockwiseDistance",n,p,q);
    private static Formula Ite(Formula p,Formula a,Formula b) => Call("ite",Parenthesized(p),a,b);
    private static Formula VectorTable(string name,Formula a,Formula b,Formula c,Formula d)
    {
        Formula v=F.Id("v");
        return Disp(All("v",Named("Vec"),Eq(Call(name,v),
            Ite(Eq(v,NegTwo()),a,Ite(Eq(v,NegOne()),b,Ite(Eq(v,PosOne()),c,d))))));
    }
    private static Formula PositiveFormula()
    {
        Formula v=F.Id("v");
        return Disp(All("v",Named("Vec"),IffF(Positive(v),Or(Eq(v,PosOne()),Eq(v,PosTwo())))));
    }
    private static Formula ConfigFormula()
    {
        Formula n=F.Id("n");
        return Disp(All("n",Nat(),Eq(Conf(n),new Formula.TypeArrow(Zmod(n),Call("Option",Named("Vec"))))));
    }
    private static Formula StoneFormula()
    {
        Formula n=F.Id("n"), N=F.Id("N"), p=F.Id("p"), v=F.Id("v");
        return Disp(All("n",Nat(),All("N",Conf(n),All("p",Zmod(n),IffF(Call("HasStone",n,N,p),Ex("v",Named("Vec"),Eq(Apply(N,p),Some(v))))))));
    }
    private static Formula DistanceFormula()
    {
        Formula n=F.Id("n"), p=F.Id("p"), q=F.Id("q");
        return Disp(All("n",Nat(),All("p",Zmod(n),All("q",Zmod(n),Eq(At(n,p,q),Call("val",Sub(q,p)))))));
    }
    private static Formula ConsecutiveFormula()
    {
        Formula n=F.Id("n"), N=F.Id("N"), p=F.Id("p"), q=F.Id("q"), r=F.Id("r");
        Formula empty=All("r",Zmod(n),Imp(LtF(D(0),At(n,p,r)),Imp(LtF(At(n,p,r),At(n,p,q)),Eq(Apply(N,r),None()))));
        Formula body=And(Ne(p,q),And(Call("HasStone",n,N,p),And(Call("HasStone",n,N,q),empty)));
        return Disp(All("n",Nat(),All("N",Conf(n),All("p",Zmod(n),All("q",Zmod(n),IffF(Call("Consecutive",n,N,p,q),body))))));
    }
    private static Formula PairFormula()
    {
        Formula d=F.Id("d"), v=F.Id("v"), w=F.Id("w");
        Formula away=Imp(Not(Positive(v)),Imp(Positive(w),Call("Odd",d)));
        Formula towards=Imp(Positive(v),Imp(Not(Positive(w)),Call("Odd",Add(Add(d,Call("length",v)),Call("length",w)))));
        Formula small=Imp(Positive(v),Imp(Not(Positive(w)),And(LeF(D(3),d),Imp(Eq(d,D(3)),And(Eq(Call("length",v),D(1)),Eq(Call("length",w),D(1)))))));
        Formula body=And(LtF(D(0),d),And(IffF(Positive(v),Not(Positive(w))),And(away,And(towards,small))));
        return Disp(All("d",Ints(),All("v",Named("Vec"),All("w",Named("Vec"),IffF(Call("PairAdmissible",d,v,w),body)))));
    }
    private static Formula NecklaceFormula()
    {
        Formula n=F.Id("n"), k=F.Id("k"), N=F.Id("N"), S=F.Id("S"), p=F.Id("p"), q=F.Id("q"), v=F.Id("v"), w=F.Id("w");
        Formula support=Ex("S",Call("Finset",Zmod(n)),And(Eq(Call("card",S),Mul(D(2),k)),All("p",Zmod(n),IffF(Member(p,S),Call("HasStone",n,N,p)))));
        Formula pairs=All("p",Zmod(n),All("q",Zmod(n),All("v",Named("Vec"),All("w",Named("Vec"),Imp(Call("Consecutive",n,N,p,q),Imp(Eq(Apply(N,p),Some(v)),Imp(Eq(Apply(N,q),Some(w)),Call("PairAdmissible",Call("ofNat",At(n,p,q)),v,w))))))));
        return Disp(All("n",Nat(),All("k",Nat(),All("N",Conf(n),IffF(Call("IsNecklace",n,k,N),And(LtF(D(0),n),And(support,pairs)))))));
    }
    private static Formula Inflow(Formula n,Formula N,Formula q)
    {
        Formula a=F.Id("a");
        return Ex("a",Seq(Zmod(n),Times,Named("Vec")),And(Eq(Apply(N,Call("fst",a)),Some(Call("snd",a))),Eq(q,Add(Call("fst",a),Parenthesized(Seq(Call("cast",Call("value",Call("snd",a))),Sp,Colon,Sp,Zmod(n)))))));
    }
    private static Formula JumpFormula()
    {
        Formula n=F.Id("n"), N=F.Id("N"), q=F.Id("q");
        Formula incoming=Inflow(n,N,q);
        Formula chosen=Call("snd",Call("choose",Parenthesized(incoming)));
        return Disp(All("n",Nat(),All("N",Conf(n),All("q",Zmod(n),Eq(Apply(Call("jumpTurn",n,N),q),Ite(incoming,Some(Call("turn",chosen)),None()))))));
    }
    private static Formula FixFormula()
    {
        Formula n=F.Id("n"), M=F.Id("M"), p=F.Id("p"), v=F.Id("v"), w=F.Id("w");
        Formula forward=Ex("w",Named("Vec"),And(Eq(Apply(M,Add(p,D(3))),Some(w)),Not(Positive(w))));
        Formula backward=Ex("w",Named("Vec"),And(Eq(Apply(M,Sub(p,D(3))),Some(w)),Positive(w)));
        Formula test=Ite(Positive(v),Parenthesized(forward),Parenthesized(backward));
        Formula present=All("v",Named("Vec"),Imp(Eq(Apply(M,p),Some(v)),Eq(Apply(Call("fix",n,M),p),Ite(test,Some(Call("shorten",v)),Some(v)))));
        Formula empty=Imp(Eq(Apply(M,p),None()),Eq(Apply(Call("fix",n,M),p),None()));
        return Disp(All("n",Nat(),All("M",Conf(n),All("p",Zmod(n),And(empty,present)))));
    }
    private static Formula TransformationFormula()
    {
        Formula n=F.Id("n"), N=F.Id("N");
        return Disp(All("n",Nat(),All("N",Conf(n),Eq(Call("necklaceT",n,N),Call("fix",n,Call("jumpTurn",n,N))))));
    }
    private static Formula ActionFormula()
    {
        Formula n=F.Id("n"), g=F.Id("g"), c=F.Id("c"), N=F.Id("N"), q=F.Id("q");
        Formula rot=Imp(Eq(g,Call("r",c)),Eq(Apply(Call("circleIsometryAct",n,g,N),q),Apply(N,Sub(q,c))));
        Formula refl=Imp(Eq(g,Call("sr",c)),Eq(Apply(Call("circleIsometryAct",n,g,N),q),Call("map",Named("negate"),Apply(N,Add(Seq(Minus,q),c)))));
        return Disp(All("n",Nat(),All("g",Call("DihedralGroup",n),All("c",Zmod(n),All("N",Conf(n),All("q",Zmod(n),And(rot,refl)))))));
    }
    private static Formula SmulFormula()
    {
        Formula n=F.Id("n"), g=F.Id("g"), N=F.Id("N");
        return Disp(All("n",Nat(),All("g",Call("DihedralGroup",n),All("N",Conf(n),Eq(Call("smul",Call("circleIsometrySMul",n),g,N),Call("circleIsometryAct",n,g,N))))));
    }
    private static Formula ClaimFormula()
    {
        Formula n=F.Id("n"), k=F.Id("k"), N=F.Id("N"), g=F.Id("g");
        Formula conclusion=Ex("g",Call("DihedralGroup",n),Eq(Apply(Call("iterate",Call("necklaceT",n),Sub(n,Mul(D(3),k))),N),Seq(g,Sp,Cdot,Sp,N)));
        return Disp(IffF(F.Id("claim"),All("n",Nat(),All("k",Nat(),Imp(Call("Even",n),Imp(LeF(D(1),k),All("N",Conf(n),Imp(Call("IsNecklace",n,k,N),conclusion))))))));
    }
}
