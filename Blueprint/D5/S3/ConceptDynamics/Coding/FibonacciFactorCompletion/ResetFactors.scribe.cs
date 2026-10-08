using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class ResetFactorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetFactors.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll,[..v],p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[..v],p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula And(params Formula[] p)
    {
        var r=p[^1];for(var k=p.Length-2;k>=0;--k)r=new Formula.Logic(p[k],FormulaLogicOperator.And,r);return r;
    }
    private static Formula Nat => I("Nat");
    private static Formula Int => I("Int");
    private static Formula Real => I("Real");
    private static Formula Letters => Call("List",I("CuLetter"));
    private static Formula Returns => Call("List",I("Return"));
    private static Formula Fn(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Sequences => Fn(Int,I("CuLetter"));
    private static Formula Language => Call("Set",Sequences);
    private static Formula Ap(Formula f,Formula x) => Call("apply",f,x);
    private static Formula Add(Formula a,Formula b) => Call("add",a,b);
    private static Formula Sub(Formula a,Formula b) => Call("subtract",a,b);
    private static Formula Mul(Formula a,Formula b) => Call("multiply",a,b);
    private static Formula Div(Formula a,Formula b) => Call("divide",a,b);
    private static Formula Pow(Formula a,Formula b) => Call("power",a,b);
    private static Formula Lt(Formula a,Formula b) => Call("lt",a,b);
    private static Formula Le(Formula a,Formula b) => Call("le",a,b);
    private static Formula Mem(Formula a,Formula b) => Call("member",a,b);
    private static Formula Len(Formula a) => Call("length",a);
    private static Formula Val(Formula a) => Call("val",a);
    private static Formula Weight(Formula a) => Call("wordWeight",a);
    private static Formula ListWeight(Formula a) => Call("listWeight",a);
    private static Formula Cast(Formula a) => Call("toReal",a);
    private static Formula IntCast(Formula a) => Call("toInt",a);
    private static Formula Card(Formula a) => Call("NatCard",a);
    private static Formula Count(Formula x,Formula t) => Call("factorCount",x,t);
    private static Formula Rate(Formula x) => Call("weightedFactorRate",x);
    private static Formula Finite(Formula x) => Call("Finite",x);
    private static Formula Injective(Formula x) => Call("FunctionInjective",x);
    private static Formula Occurs(Formula omega,Formula w) => Call("Occurs",omega,w);
    private static Formula Factor(Formula x,Formula w) => Ex(And(Mem(I("omega"),x),Occurs(I("omega"),w)),B("omega",Sequences));
    private static Formula Subtype(string name,Formula type,Formula predicate) => Call("Subtype",new Formula.Sequence(predicate,I(name),type));
    private static Formula Lambda(string name,Formula type,Formula body) => new Formula.Sequence(body,I(name),type);
    private static Formula Dictionary(Formula x,Formula t) => Call("FactorDictionary",x,t);
    private static Formula Log(Formula x) => Call("logb",D(2),Cast(x));
    private static Formula MaxOne(Formula x) => Call("max",D(1),x);
    private static Formula Reset(Formula r,Formula ws) => Call("resetFactor",r,ws);
    private static Formula MapVal(Formula xs) => Call("map",I("val"),xs);
    private static Formula Lower => Call("LowerMemoryLanguage",I("n"),I("K"),Threshold);
    private static Formula H => Call("hSide",I("high"));
    private static Formula A => Call("aSide",I("high"));
    private static Formula Scale => Mul(Pow(I("g"),D(2)),Pow(I("chi"),I("K")));
    private static Formula Threshold => Div(Div(Sub(I("lam"),I("b")),Pow(I("g"),D(2))),Pow(I("chi"),I("K")));
    private static Formula Start => Call("initial",I("high"),I("sourceModel"));
    private static Formula Delta => Sub(Sub(H,Mul(Pow(I("rho"),Call("m",I("R"))),Sub(H,Mul(I("chi"),A)))),Start);
    private static Formula Gamma => Mul(Delta,Pow(I("g"),I("N")));
    private static Formula Epsilon => Div(Call("min",Sub(I("b"),Call("actualAutomaticCost",I("K"))),Mul(Scale,Gamma)),D(2));
    private static Formula BlockWeight => Add(Add(I("N"),D(2,0)),Mul(D(6),Call("m",I("R"))));
    private static Formula Trace(Formula d,Formula xs) => Call("GuardTrace",I("K"),d,I("false"),I("high"),xs,Start);
    private static Formula Book => Subtype("xs",Returns,And(Trace(Threshold,I("xs")),Equal(ListWeight(I("xs")),I("N"))));
    private static Formula ChoiceType => Fn(Call("Fin",I("q")),Book);
    private static Formula ChoiceFactor => Lambda("z",ChoiceType,Reset(I("R"),Call("ofFn",Lambda("i",Call("Fin",I("q")),Val(Ap(I("z"),I("i")))))));
    private static Formula ChosenWord => Ap(ChoiceFactor,I("z"));
    private static Formula FullWeight => Mul(I("q"),BlockWeight);
    private static Formula Valid(Formula w) => And(Equal(Weight(w),FullWeight),Factor(Lower,w));

    private static Formula DictionaryDefinition() => Disp(All(Equal(Dictionary(I("X"),I("T")),
        Subtype("w",Letters,And(Factor(I("X"),I("w")),Equal(Weight(I("w")),I("T"))))),B("X",Language),B("T",Nat)));
    private static Formula CountDefinition() => Disp(All(Equal(Count(I("X"),I("T")),Card(Dictionary(I("X"),I("T")))),B("X",Language),B("T",Nat)));
    private static Formula RateDefinition() => Disp(All(Equal(Rate(I("X")),Call("FilterLimsup",
        Lambda("T",Nat,Div(Log(MaxOne(Count(I("X"),I("T")))),Cast(I("T")))),I("atTop"))),B("X",Language)));
    private static Formula ResetDefinition() => Disp(All(Equal(Reset(I("R"),I("words")),Call("flatten",Call("map",
        Lambda("xs",Returns,Call("executionWord",Call("cons",I("R"),I("xs")))),I("words")))),B("R",I("Return")),B("words",Call("List",Returns))));
    private static Formula GeometryStatement() => Disp(And(
        All(Equal(Weight(Call("append",I("w"),I("v"))),Add(Weight(I("w")),Weight(I("v")))),B("w",Letters),B("v",Letters)),
        All(Le(Len(I("w")),Weight(I("w"))),B("w",Letters)),
        All(Imp(Equal(Weight(I("w")),D(0)),Equal(I("w"),Call("nil"))),B("w",Letters))));
    private static Formula BoundStatement() => Disp(All(And(Finite(Dictionary(I("X"),I("T"))),
        Le(Count(I("X"),I("T")),Pow(D(3),Add(I("T"),D(1))))),B("X",Language),B("T",Nat)));
    private static Formula ConcatenationStatement()
    {
        var words=Call("List",Subtype("w",Letters,Equal(Weight(I("w")),I("L"))));
        return Disp(All(Imp(Lt(D(0),I("L")),Injective(Lambda("words",words,Call("flatten",MapVal(I("words")))))),B("L",Nat)));
    }
    private static Formula ParserStatement()
    {
        var v=Subtype("xs",Returns,And(Ap(I("p"),I("xs")),Equal(ListWeight(I("xs")),I("N"))));
        var words=Call("List",v);var word=Reset(I("R"),MapVal(I("words")));
        var l=Add(Add(I("N"),Mul(D(2,0),Call("r",I("R")))),Mul(D(6),Call("m",I("R"))));
        return Disp(All(And(Injective(Lambda("words",words,word)),All(Equal(Weight(word),Mul(Len(I("words")),l)),B("words",words))),
            B("R",I("Return")),B("N",Nat),B("p",Fn(Returns,I("Prop")))));
    }
    private static Formula TiledStatement()
    {
        var w=I("W");var cut=Call("blockCut",w,I("j"));var at=Ap(w,I("j"));
        var tiles=All(Equal(Ap(I("omega"),Add(cut,IntCast(I("k")))),Call("getElem",at,I("k"))),B("j",Int),B("k",Call("Fin",Len(at))));
        var window=Call("blockWindow",w,I("a"),I("q"));
        return Disp(All(Imp(And(All(Lt(D(0),Len(at)),B("j",Int)),tiles),All(Equal(
            Ap(I("omega"),Add(Call("blockCut",w,I("a")),IntCast(I("k")))),Call("getElem",window,I("k"))),B("k",Call("Fin",Len(window))))),
            B("W",Fn(Int,Letters)),B("omega",Sequences),B("a",Int),B("q",Nat)));
    }
    private static Formula ChoiceStatement() => Disp(All(Equal(Call("choiceWindow",I("choices"),I("a"),I("q")),Call("ofFn",
        Lambda("i",Call("Fin",I("q")),Ap(I("choices"),Add(I("a"),IntCast(I("i"))))))),B("V",I("Type")),B("choices",Fn(Int,I("V"))),B("a",Int),B("q",Nat)));
    private static Formula RateStatement() => Disp(All(Imp(And(Lt(D(0),I("L")),All(Le(Pow(I("a"),I("q")),Count(I("X"),Mul(I("q"),I("L")))),B("q",Nat))),
        Le(Div(Log(MaxOne(I("a"))),Cast(I("L"))),Rate(I("X")))),B("X",Language),B("a",Nat),B("L",Nat)));
    private static Formula Packet()
    {
        var family=I("family");var w=I("w");var z=I("z");
        return And(Injective(ChoiceFactor),All(Valid(ChosenWord),B("z",ChoiceType)),
            Ex(And(Equal(Call("card",family),Pow(Card(Book),I("q"))),
                All(Iff(Mem(w,family),Ex(Equal(ChosenWord,w),B("z",ChoiceType))),B("w",Letters)),
                All(Imp(Mem(w,family),Valid(w)),B("w",Letters))),B("family",Call("Finset",Letters))),
            Le(Pow(Card(Book),I("q")),Count(Lower,FullWeight)));
    }
    private static Formula FiniteJoint()
    {
        var execution=Call("resetConcatenation",I("R"),MapVal(I("words")));
        return All(And(Call("GuardTrace",I("K"),Add(Threshold,Gamma),I("false"),I("high"),execution,
            Call("initial",I("high"),I("targetModel"))),
            Call("ActualPairSupply",I("targetModel"),I("o"),Sub(I("b"),Epsilon),I("strict"),execution)),
            B("targetModel",I("Model")),B("words",Call("List",Book)));
    }
    private static Formula Bilateral()
    {
        var w=Lambda("j",Int,Call("executionWord",Call("cons",I("R"),Val(Ap(I("choices"),I("j"))))));
        var cut=Call("blockCut",w,I("j"));var block=Ap(w,I("j"));
        var tiles=All(Equal(Ap(I("omega"),Add(cut,IntCast(I("k")))),Call("getElem",block,I("k"))),
            B("j",Int),B("k",Call("Fin",Len(block))));
        var guards=All(Call("GuardTrace",I("K"),Add(Threshold,Gamma),I("false"),I("high"),
            Call("cons",I("R"),Val(Ap(I("choices"),I("j")))),Call("pastState",I("omega"),cut)),B("j",Int));
        return All(Ex(And(Mem(I("omega"),Call("AuxiliaryLanguage",I("K"),Add(Threshold,Gamma))),
            Mem(I("omega"),Lower),tiles,guards),B("omega",Sequences)),B("choices",Fn(Int,Book)));
    }
    private static Formula MainStatement()
    {
        var budget=And(Le(D(2),I("K")),Lt(Sub(I("lam"),Mul(Scale,H)),I("b")),
            Lt(I("b"),Sub(I("lam"),Mul(Scale,Div(A,Sub(D(1),Mul(I("rho"),Pow(I("chi"),I("K")))))))));
        var memory=And(Le(I("K"),I("n")),Lt(Mul(H,Pow(I("rho"),I("n"))),Mul(Pow(I("chi"),Sub(I("K"),D(1))),Gamma)),
            Bilateral(),All(Packet(),B("q",Nat)),Le(Div(Log(MaxOne(Card(Book))),Cast(BlockWeight)),Rate(Lower)));
        var body=And(Lt(D(0),Delta),Lt(D(0),Gamma),Lt(D(0),Epsilon),Finite(Book),FiniteJoint(),Ex(memory,B("n",Nat)));
        var floor=Sub(H,Mul(Pow(I("rho"),Call("m",I("R"))),Sub(H,Mul(I("chi"),A))));
        return Disp(All(Imp(budget,Ex(And(Equal(Call("r",I("R")),D(1)),
            Lt(Call("max",Call("max",Call("xSide",I("high")),Call("ySide",I("high"))),Threshold),floor),All(Imp(Lt(D(0),I("N")),body),
            B("sourceModel",I("Model")),B("N",Nat))),B("R",I("Return")))),B("o",I("Ownership")),B("b",Real),B("K",Nat)));
    }
    private static DocumentBlock Node(string name,Formula formula,string prose,bool definition=false) => Describe.Lean(
        DescribeId.Create("fib-reset-factors-"+name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(name.Replace('_',' ')),
        StatementSource.FromAuthor(formula),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),definition?DescribeRole.Definition:DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original equal-weight weak codebook has distinct factors in one lower-memory language, with exact reset overhead and a weighted limsup bound.",
        H("Same-reset weighted factor dictionaries"),Blocks(
        Node("FactorDictionary",DictionaryDefinition(),"The dictionary contains every word of exact original weight T that occurs in a bilateral sequence of X. Occurrence retains a single sequence and one integer starting position; transient graph paths are not substituted.",true),
        Node("factorCount",CountDefinition(),"The count is the natural cardinality of that entire factor dictionary, including the empty word at weight zero when the language is nonempty.",true),
        Node("weightedFactorRate",RateDefinition(),"The rate is the real upper limit over total actual weight T, with max(1,count) and total real division at T=0. It uses the original weights 20 and 6, rather than letter length.",true),
        Node("resetFactor",ResetDefinition(),"Every finite ordered choice receives the same original reset before its execution word. Flattening concatenates these words without prescribing a common letter length.",true),
        Node("word_weight_geometry",GeometryStatement(),"Original letter weights are positive and additive. A zero-weight word is empty; letter length is bounded by its actual weight."),
        Node("factor_dictionary_bound",BoundStatement(),"Every word of weight T has at most T letters. Its optional letters at the first T+1 indices determine it uniquely, giving a finite dictionary and the bound 3 to T+1."),
        Node("equal_weight_concatenation_injective",ConcatenationStatement(),"At each common accumulated positive weight, prefix comparison recovers the next whole block. This proves unique parsing with variable block letter lengths; equality of weights never asserts equality of lengths."),
        Node("reset_factor_parser",ParserStatement(),"The existing complete execution-word parser identifies each original return list after the fixed reset is removed. Equal weighted cuts identify the ordered choices. No reset exponent restriction is needed here; the weight includes the actual r(R)."),
        Node("tiled_window_occurs",TiledStatement(),"The indexed tiling supplies every letter of each consecutive finite block window at its original integer cut. All blocks, including the negative-index past, belong to the same bilateral realization."),
        Node("choice_window_ofFn",ChoiceStatement(),"The recursive finite choice window equals the list of choices at consecutive integer indices a through a+q-1."),
        Node("factor_rate_of_power_count",RateStatement(),"The finite alphabet supplies a uniform bound on the real logarithmic quotients. Counts at all multiples of a positive L give a frequent lower bound and hence the weighted limsup bound. Empty and singleton codebooks have the displayed zero lower bound."),
        Node("same_reset_factor_cardinality",MainStatement(),"One reset with r=1 has floor B above both actual initial states and d, and is fixed before both source models and all N>0. For the full weak codebook, delta=B-D0 and gamma=delta times g to N. Every finite choice has high guard d+gamma and actual strict supply with the positive half-minimum error margin, including the original zero-error futures. The same reset admits every bilateral choice on one sequence with all block guards, in one lower-memory language n chosen after the fixed codebook. Here n is at least K and h rho to n is below chi to K-1 times gamma. For every q, the choice map is injective, its exact-weight image has cardinality a to q, and every image word extends bilaterally in that same lower language. The resulting weighted rate is at least log base two of max(1,a), divided by N+20+6m(R). Positive accumulated-weight cuts recover the choices even when their letter lengths differ. The empty choice q=0 uses the all-u sequence."))));
}
