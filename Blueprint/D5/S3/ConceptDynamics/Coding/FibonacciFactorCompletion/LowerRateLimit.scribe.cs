using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class LowerRateLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/LowerRateLimit.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll,[..v],p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[..v],p);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula And(params Formula[] p)
    {
        var r=p[^1];for(var k=p.Length-2;k>=0;--k)r=new Formula.Logic(p[k],FormulaLogicOperator.And,r);return r;
    }
    private static Formula Nat => I("Nat");
    private static Formula Int => I("Int");
    private static Formula Real => I("Real");
    private static Formula Letters => Call("List",I("CuLetter"));
    private static Formula Fn(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Seq => Fn(Int,I("CuLetter"));
    private static Formula Lambda(string n,Formula t,Formula p) => new Formula.Sequence(p,I(n),t);
    private static Formula Ap(Formula f,Formula x) => Call("apply",f,x);
    private static Formula Add(Formula a,Formula b) => Call("add",a,b);
    private static Formula Sub(Formula a,Formula b) => Call("subtract",a,b);
    private static Formula Mul(Formula a,Formula b) => Call("multiply",a,b);
    private static Formula Div(Formula a,Formula b) => Call("divide",a,b);
    private static Formula Pow(Formula a,Formula b) => Call("power",a,b);
    private static Formula Lt(Formula a,Formula b) => Call("lt",a,b);
    private static Formula Le(Formula a,Formula b) => Call("le",a,b);
    private static Formula Val(Formula a) => Call("val",a);
    private static Formula Cast(Formula a) => Call("toReal",a);
    private static Formula Mem(Formula a,Formula b) => Call("member",a,b);
    private static Formula Len(Formula a) => Call("length",a);
    private static Formula Fin(Formula a) => Call("Fin",a);
    private static Formula Injective(Formula a) => Call("FunctionInjective",a);
    private static Formula Weight(Formula a) => Call("listWeight",a);
    private static Formula Log(Formula a) => Call("logb",D(2),Cast(a));
    private static Formula Hh => Call("hSide",I("high"));
    private static Formula A => Call("aSide",I("high"));
    private static Formula Threshold => Div(Div(Sub(I("lam"),I("b")),Pow(I("g"),D(2))),Pow(I("chi"),I("K")));
    private static Formula Scale => Mul(Pow(I("g"),D(2)),Pow(I("chi"),I("K")));
    private static Formula Floor => Sub(Hh,Mul(Pow(I("rho"),Call("m",I("R"))),Sub(Hh,Mul(I("chi"),A))));
    private static Formula Delta => Sub(Floor,Call("initial",I("high"),I("model")));
    private static Formula Gain => Mul(Delta,Pow(I("g"),I("N")));
    private static Formula Error => Div(Call("min",Sub(I("b"),Call("actualAutomaticCost",I("K"))),Mul(Scale,Gain)),D(2));
    private static Formula L => Add(Add(I("N"),D(2,0)),Mul(D(6),Call("m",I("R"))));
    private static Formula Book => Call("ActualDictionary",I("model"),I("K"),Threshold,I("false"),I("N"));
    private static Formula Count(Formula t,Formula strict) => Call("actualCount",I("model"),I("K"),Threshold,strict,t);
    private static Formula Eta => Call("etaB",I("K"),I("b"));
    private static Formula Trace(Formula d,Formula strict,Formula xs,Formula model) => Call("GuardTrace",I("K"),d,strict,I("high"),xs,Call("initial",I("high"),model));
    private static Formula Supply(Formula model,Formula b,Formula xs) => Call("ActualPairSupply",model,I("o"),b,I("strict"),xs);
    private static Formula Lower(Formula n) => Call("MemoryLanguage",I("lower"),n,I("K"),Threshold);
    private static Formula LowerRate(Formula n) => Call("weightedFactorRate",Lower(n));
    private static Formula Tendsto(Formula f,Formula y, bool infinity=false) => Call("Tendsto",f,I("atTop"),infinity?I("atTop"):Call("nhds",y));
    private static Formula Budget => And(Le(D(2),I("K")),Lt(Sub(I("lam"),Mul(Scale,Hh)),I("b")),
        Lt(I("b"),Sub(I("lam"),Mul(Scale,Div(A,Sub(D(1),Mul(I("rho"),Pow(I("chi"),I("K")))))))));
    private static Formula UnderBudget(Formula p) => All(Imp(Budget,p),B("o",I("Ownership")),B("b",Real),B("K",Nat));
    private static Formula LowZ => Call("lowChoices",I("z"));
    private static Formula BinaryChoices => Fn(Fin(I("q")),I("Bool"));
    private static Formula LowMap => Lambda("z",BinaryChoices,LowZ);
    private static Formula LowDefinition() => Disp(All(Equal(Call("lowReturns",I("choice")),
        Call("ifThenElse",I("choice"),Call("list",Call("Return",D(2),D(1)),Call("Return",D(1),D(1))),
            Call("list",Call("Return",D(1),D(1)),Call("Return",D(2),D(1))))),B("choice",I("Bool"))));
    private static Formula ChoicesDefinition() => Disp(All(Equal(LowZ,Call("flatten",Call("ofFn",
        Lambda("i",Fin(I("q")),Call("lowReturns",Ap(I("z"),I("i"))))))),B("q",Nat),B("z",BinaryChoices)));
    private static Formula LowCountStatement() => Disp(UnderBudget(All(And(
        Injective(LowMap),Injective(Lambda("z",BinaryChoices,Call("history",I("model"),LowZ))),
        All(And(Equal(Weight(LowZ),Mul(I("q"),D(5,8))),Supply(I("model"),I("b"),LowZ)),B("z",BinaryChoices)),
        All(Le(Pow(D(2),I("q")),Count(Mul(I("q"),D(5,8)),I("strictFlag"))),B("strictFlag",I("Bool")))),
        B("model",I("Model")),B("q",Nat))));
    private static Formula PositiveStatement() => Disp(UnderBudget(All(Le(Div(D(1),D(5,8)),
        Call("actualRate",I("model"),I("K"),Threshold,I("strictFlag"))),B("model",I("Model")),B("strictFlag",I("Bool")))));
    private static Formula Occurrence(Formula w) => Ex(And(Mem(I("omega"),Lower(I("n"))),Call("Occurs",I("omega"),w)),B("omega",Seq));
    private static Formula Bilateral()
    {
        var w=Call("executionWord",Call("cons",I("R"),Val(Ap(I("choices"),I("j")))));
        var ws=Lambda("j",Int,w);
        var cut=Call("blockCut",ws,I("j"));
        var tile=All(Equal(Ap(I("omega"),Add(cut,Call("toInt",Val(I("k"))))),Call("getElem",w,I("k"))),
            B("j",Int),B("k",Fin(Len(w))));
        var guards=All(Call("GuardTrace",I("K"),Add(Threshold,Gain),I("false"),I("high"),
            Call("cons",I("R"),Val(Ap(I("choices"),I("j")))),Call("pastState",I("omega"),cut)),B("j",Int));
        return All(Ex(And(Mem(I("omega"),Call("AuxiliaryLanguage",I("K"),Add(Threshold,Gain))),
            Mem(I("omega"),Lower(I("n"))),tile,guards),B("omega",Seq)),B("choices",Fn(Int,Book)));
    }
    private static Formula Powers()
    {
        var choices=Fn(Fin(I("q")),Book);
        var f=Lambda("z",choices,Call("resetFactor",I("R"),Call("ofFn",Lambda("i",Fin(I("q")),Val(Ap(I("z"),I("i")))))));
        var w=Ap(f,I("z"));
        var valid=And(Equal(Call("wordWeight",I("w")),Mul(I("q"),L)),Occurrence(I("w")));
        var family=Ex(And(Equal(Call("card",I("family")),Pow(Call("NatCard",Book),I("q"))),
            All(Iff(Mem(I("w"),I("family")),Ex(Equal(w,I("w")),B("z",choices))),B("w",Letters)),
            All(Imp(Mem(I("w"),I("family")),valid),B("w",Letters))),B("family",Call("Finset",Letters)));
        return All(And(Injective(f),All(And(Equal(Call("wordWeight",w),Mul(I("q"),L)),Occurrence(w)),B("z",choices)),
            family,Le(Pow(Call("NatCard",Book),I("q")),Call("factorCount",Lower(I("n")),Mul(I("q"),L)))),B("q",Nat));
    }
    private static Formula Actual()
    {
        var execution=Call("resetConcatenation",I("R"),Call("map",I("val"),I("words")));
        return All(And(Trace(Add(Threshold,Gain),I("false"),execution,I("targetModel")),
            Supply(I("targetModel"),Sub(I("b"),Error),execution)),B("targetModel",I("Model")),B("words",Call("List",Book)));
    }
    private static Formula FixedBody() => And(Lt(D(0),Delta),Lt(D(0),Gain),Lt(D(0),Error),Call("Finite",Book),Actual(),
        Ex(And(Le(I("K"),I("n")),Lt(Mul(Hh,Pow(I("rho"),I("n"))),Mul(Pow(I("chi"),Sub(I("K"),D(1))),Gain)),
            Bilateral(),Powers(),Le(Div(Log(Call("max",D(1),Call("NatCard",Book))),Cast(L)),LowerRate(I("n")))),B("n",Nat)));
    private static Formula FixedStatement() => Disp(All(Iff(Call("FixedCodebook",I("R"),I("o"),I("b"),I("K"),I("model"),I("N")),FixedBody()),
        B("R",I("Return")),B("o",I("Ownership")),B("b",Real),B("K",Nat),B("model",I("Model")),B("N",Nat)));
    private static Formula Nj => Ap(I("N"),I("j"));
    private static Formula Lj => Add(Add(Nj,D(2,0)),Mul(D(6),Call("m",I("R"))));
    private static Formula ApproximationStatement()
    {
        var sequence=And(Tendsto(I("N"),D(0),true),All(And(Lt(D(0),Nj),Le(D(1),Count(Nj,I("false")))),B("j",Nat)),
            Tendsto(Lambda("j",Nat,Div(Log(Count(Nj,I("false"))),Cast(Nj))),Eta),
            Tendsto(Lambda("j",Nat,Div(Cast(Nj),Cast(Lj))),D(1)),
            Tendsto(Lambda("j",Nat,Div(Log(Count(Nj,I("false"))),Cast(Lj))),Eta),
            All(Call("FixedCodebook",I("R"),I("o"),I("b"),I("K"),I("model"),Nj),B("j",Nat)));
        return Disp(UnderBudget(Ex(And(Equal(Call("r",I("R")),D(1)),
            Lt(Call("max",Call("max",Call("xSide",I("high")),Call("ySide",I("high"))),Threshold),Floor),
            All(Ex(sequence,B("N",Fn(Nat,Nat))),B("model",I("Model")))),B("R",I("Return")))));
    }
    private static Formula LimitStatement()
    {
        var lower=Lambda("n",Nat,LowerRate(I("n")));
        var lowerRoot=Ap(Ap(I("roots"),I("lower")),I("n"));
        var upperRoot=Ap(Ap(I("roots"),I("upper")),I("n"));
        var lowerGamma=Call("negate",Call("logb",D(2),lowerRoot));
        var upperGamma=Call("negate",Call("logb",D(2),upperRoot));
        var root=Ap(Ap(I("roots"),I("side")),I("n"));
        var gamma=Call("negate",Call("logb",D(2),root));
        var rootProperties=All(Imp(Le(I("K"),I("n")),And(Lt(D(0),root),Lt(root,D(1)),
            Equal(Call("weightedRadius",I("side"),I("n"),I("K"),Threshold,root),D(1)),
            Equal(Call("weightedFactorRate",Call("MemoryLanguage",I("side"),I("n"),I("K"),Threshold)),gamma))),
            B("side",I("MemorySide")),B("n",Nat));
        var roots=Ex(And(rootProperties,
            All(Imp(Le(I("K"),I("n")),And(Le(lowerGamma,Eta),Le(Eta,upperGamma))),B("n",Nat)),
            Call("MonotoneOn",Lambda("n",Nat,lowerGamma),Call("Ici",I("K"))),
            Call("AntitoneOn",Lambda("n",Nat,upperGamma),Call("Ici",I("K"))),
            Tendsto(Lambda("n",Nat,upperGamma),Eta),
            Tendsto(Lambda("n",Nat,Call("negate",Call("logb",D(2),
                Ap(Ap(I("roots"),I("lower")),Add(I("n"),I("K")))))),Eta),
            All(Equal(Call("actualRate",I("model"),I("K"),Threshold,I("strictFlag")),Eta),
                B("model",I("Model")),B("strictFlag",I("Bool")))),B("roots",Fn(I("MemorySide"),Fn(Nat,Real))));
        var uniform=All(Imp(Lt(D(0),I("epsilon")),Ex(And(Le(I("K"),I("n0")),
            All(Imp(Le(I("n0"),I("n")),And(Lt(Sub(Eta,I("epsilon")),LowerRate(I("n"))),Le(LowerRate(I("n")),Eta))),B("n",Nat))),B("n0",Nat))),B("epsilon",Real));
        return Disp(UnderBudget(And(Le(Div(D(1),D(5,8)),Eta),Call("Monotone",lower),uniform,Tendsto(lower,Eta),roots)));
    }
    private static DocumentBlock Node(string name,Formula formula,string prose,bool definition=false) => Describe.Lean(
        DescribeId.Create("fib-lower-rate-"+name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(name.Replace('_',' ')),
        StatementSource.FromAuthor(formula),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),definition?DescribeRole.Definition:DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual complete low words have positive rate, and codebooks from the original weak limsup approximate that rate with one fixed reset. The original lower-memory rates converge increasingly to the same value.",
        H("Actual codebooks and the lower rate limit"),Blocks(
        Node("lowReturns",LowDefinition(),"The false choice is the complete return list (1,1),(2,1), and the true choice is (2,1),(1,1). Both m and r are positive. Their execution words are exactly c u c u u and c u u c u, and each has weight 58. Execution goes from the original tail toward the outside; the literal source uses the reversed list and retains each original block's label order.",true),
        Node("lowChoices",ChoicesDefinition(),"Flatten the chosen complete lists in their finite execution order. The empty choice has the empty list and weight zero. Both actual initial models retain their original high and low tails, with observation offsets 26 and 52.",true),
        Node("actual_low_choice_count",LowCountStatement(),"Every return has r=1<K, so every finite choice is strictly legal from either actual start. The actual paired-source supply includes the common prescribed history, all departure slots, and each original tail with zero future error. Positive weighted cuts and the complete execution parser recover every binary choice; the original history parser also distinguishes them. There are at least 2 to q strict lists and at least as many weak lists at weight 58q, including q=0 and q=1."),
        Node("actual_rate_positive",PositiveStatement(),"Actual counts at unbounded multiples of 58 give a frequent normalized logarithmic lower bound of 1/58. This is the original actual rate for both starts and both guard flags, rather than a rate per letter."),
        Node("FixedCodebook",FixedStatement(),"The dictionary contains every original weak list of exact weight N. Its reset floor B, delta=B-D0, gain=delta times g to N, and positive half-minimum error are kept together. All finite actual choices share the strengthened guard and the strict budget b-error, with original zero-error futures. One memory n is selected after that entire fixed dictionary and satisfies n>=K and h rho to n<chi to K-1 times gain. Every bilateral choice has one sequence for its auxiliary membership, lower-memory membership, tiling at every integer cut, and all block guards. These auxiliary infinite sequences are distinct from the finite actual sources. For every q, positive cumulative-weight cuts give an injective choice map, its exact-weight image, cardinality a to q and bilateral occurrence in that same lower language. These conditions characterize the displayed proposition.",true),
        Node("original_count_codebook_approximation",ApproximationStatement(),"One reset is selected before either source model or any weight. The bounded original weak logarithmic sequence has a limsup sequence tending to infinity. Actual positivity makes its weights and counts positive after discarding only a finite prefix. Thus max(1,count) equals count throughout the retained sequence. The ratio N/(N+20+6m(R)) tends to one, so both the raw normalized logarithm and the fixed-overhead codebook slope tend to eta_b. Each codebook retains its complete finite actual and bilateral package; its common margin is obtained before its memory is selected."),
        Node("original_lower_rate_limit",LimitStatement(),"For any positive epsilon, fix one codebook whose slope exceeds eta_b-epsilon, then select its memory n_j. Lower-memory monotonicity preserves that bound for every n>=max(K,n_j). The actual-to-auxiliary rate equality gives the common upper bound eta_b, so the lower rates increase to eta_b. The nested-language theorem supplies the same actual eta_b for the upper rates, which decrease to eta_b. One original root family records both exact MemoryLanguage sides on n>=K, their radius-one equations and rate identities, the lower and upper root monotonicities, and the natural lower n+K shift. It also retains the actual model and strict/weak contract rate equalities. Codebook margins may shrink as N grows; the statement selects memory separately for each fixed codebook."))));
}
