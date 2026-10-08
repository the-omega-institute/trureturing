using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class ActualCountRateBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ActualCountRateBridge.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists, [..v], p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula And(params Formula[] p) { var r=p[^1]; for(var k=p.Length-2;k>=0;--k) r=new Formula.Logic(p[k],FormulaLogicOperator.And,r); return r; }
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula Bool => I("Bool");
    private static Formula Model => I("Model");
    private static Formula Ret => I("Return");
    private static Formula List(Formula t) => Call("List",t);
    private static Formula Lists => List(Ret);
    private static Formula Word => List(I("CuLetter"));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Config => Fn(I("Int"),I("CuLetter"));
    private static Formula Add(Formula a, Formula b) => Call("add",a,b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract",a,b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply",a,b);
    private static Formula Div(Formula a, Formula b) => Call("divide",a,b);
    private static Formula Pow(Formula a, Formula b) => Call("power",a,b);
    private static Formula Le(Formula a, Formula b) => Call("le",a,b);
    private static Formula Lt(Formula a, Formula b) => Call("lt",a,b);
    private static Formula Max(Formula a, Formula b) => Call("max",a,b);
    private static Formula Val(Formula a) => Call("val",a);
    private static Formula Field(string f, Formula a) => Call(f,a);
    private static Formula R(Formula a) => Call("toReal",a);
    private static Formula Lam(string n, Formula t, Formula p) => new Formula.Sequence(p,I(n),t);
    private static Formula If(Formula p, Formula a, Formula b) => Call("ifThenElse",p,a,b);
    private static Formula Append(Formula a, Formula b) => Call("append",a,b);
    private static Formula Cons(Formula a, Formula b) => Call("cons",a,b);
    private static Formula Rep(Formula n, Formula a) => Call("replicate",n,a);
    private static Formula Weight(Formula a) => Call("listWeight",a);
    private static Formula WWeight(Formula a) => Call("wordWeight",a);
    private static Formula EWord(Formula a) => Call("executionWord",a);
    private static Formula Initial(Formula model) => Call("initial",I("high"),model);
    private static Formula HS => Call("hSide",I("high"));
    private static Formula AS => Call("aSide",I("high"));
    private static Formula D => Div(Div(Sub(I("lam"),I("b")),Pow(I("g"),F.D(2))),Pow(I("chi"),I("K")));
    private static Formula Aux(Formula d) => Call("AuxiliaryLanguage",I("K"),d);
    private static Formula Factor(Formula d, Formula n) => Call("FactorDictionary",Aux(d),n);
    private static Formula FCount(Formula d, Formula n) => Call("factorCount",Aux(d),n);
    private static Formula FRate(Formula d) => Call("weightedFactorRate",Aux(d));
    private static Formula Dict(Formula model, Formula d, Formula strict, Formula n) => Call("ActualDictionary",model,I("K"),d,strict,n);
    private static Formula Count(Formula model, Formula d, Formula strict, Formula n) => Call("actualCount",model,I("K"),d,strict,n);
    private static Formula Rate(Formula model, Formula d, Formula strict) => Call("actualRate",model,I("K"),d,strict);
    private static Formula Log(Formula model, Formula d, Formula strict, Formula n) => Call("actualLogRate",model,I("K"),d,strict,n);
    private static Formula Normal(Formula count, Formula n) => Div(Call("logb",F.D(2),R(Max(F.D(1),count))),R(n));
    private static Formula Guard(Formula model, Formula d, Formula strict, Formula xs) => Call("GuardTrace",I("K"),d,strict,I("high"),xs,Initial(model));
    private static Formula Supply(Formula model, Formula contract, Formula xs) => Call("ActualPairSupply",model,I("o"),I("b"),contract,xs);
    private static Formula Eta => Call("etaB",I("K"),I("b"));
    private static Formula CR => Add(F.D(2,0),Mul(F.D(6),Field("m",I("R"))));
    private static Formula BM => Sub(HS,Mul(Pow(I("rho"),Field("m",I("R"))),Sub(HS,Mul(I("chi"),AS))));
    private static Formula ResetBound => Lt(Max(Max(Call("xSide",I("high")),Call("ySide",I("high"))),D),BM);
    private static Formula LastC(Formula w) => Equal(Call("getLastOption",w),Call("some",I("c")));
    private static Formula Filled(Formula w) => If(LastC(w),Append(w,Call("singleton",I("u"))),w);
    private static Formula Completed => Call("completedList",I("R"),I("a"),I("first"),I("rest"));
    private static Formula Parsed => Append(Rep(I("a"),I("u")),EWord(Cons(I("first"),I("rest"))));
    private static Formula Budget => And(Le(F.D(2),I("K")),
        Lt(Sub(I("lam"),Mul(Mul(Pow(I("g"),F.D(2)),Pow(I("chi"),I("K"))),HS)),I("b")),
        Lt(I("b"),Sub(I("lam"),Mul(Mul(Pow(I("g"),F.D(2)),Pow(I("chi"),I("K"))),Div(AS,Sub(F.D(1),Mul(I("rho"),Pow(I("chi"),I("K")))))))));
    private static Formula Base(Formula p) => All(Imp(Budget,p),B("o",I("Ownership")),B("b",Real),B("K",Nat));
    private static Formula Mathematical(Formula p, params Formula.BoundVariable[] extra) =>
        All(p,[B("model",Model),B("K",Nat),B("d",Real),B("strict",Bool),..extra]);
    private static Formula OneCap(Formula p, params Formula.BoundVariable[] extra) => Mathematical(Imp(Le(F.D(1),I("K")),p),extra);
    private static Formula Shifted(Formula n) => Normal(Count(I("model"),I("d"),I("strict"),Add(n,I("C"))),n);
    private static Formula Bounded(Formula f) => Call("IsBoundedUnder",I("le"),I("atTop"),f);
    private static Formula Limsup(Formula f) => Call("limsup",f,I("atTop"));
    private static Formula CDict(Formula n) => Call("ContractDictionary",I("model"),I("o"),I("b"),I("contract"),n);
    private static Formula CCount(Formula n) => Call("contractCount",I("model"),I("o"),I("b"),I("contract"),n);
    private static Formula CRate => Call("contractRate",I("model"),I("o"),I("b"),I("contract"));
    private static Formula Flag => Call("contractStrict",I("o"),I("contract"));
    private static Formula CountComparison() => Ex(And(Equal(Field("r",I("R")),F.D(1)),ResetBound,
        All(Le(Count(I("src"),D,I("false"),I("N")),Count(I("dst"),D,I("true"),Add(I("N"),CR))),B("src",Model),B("dst",Model),B("N",Nat)),
        All(Le(FCount(D,I("N")),Add(Add(Count(I("model"),D,I("true"),Add(Add(I("N"),CR),F.D(6))),
            Count(I("model"),D,I("true"),Add(Add(I("N"),CR),F.D(1,2)))),F.D(1))),B("model",Model),B("N",Nat))),B("R",Ret));
    private static Formula Completion() => Ex(And(Equal(Field("r",I("R")),F.D(1)),ResetBound,
        All(Imp(Guard(I("src"),D,I("false"),I("xs")),Supply(I("dst"),I("strict"),Cons(I("R"),I("xs")))),B("src",Model),B("dst",Model),B("xs",Lists)),
        All(Imp(And(Call("AuxiliaryFactor",I("K"),D,I("w")),Call("member",I("c"),I("w"))),
            Ex(And(Equal(Filled(I("w")),Parsed),Supply(I("model"),I("strict"),Completed),
                Equal(Weight(Completed),Add(Add(WWeight(I("w")),CR),If(LastC(I("w")),F.D(1,2),F.D(6))))),B("a",Nat),B("first",Ret),B("rest",Lists))),
            B("model",Model),B("w",Word))),B("R",Ret));
    private static DocumentBlock Node(string n, Formula f, string prose, DescribeRole role=DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("fib-actual-count-"+n.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+n),
        H(n.Replace('_',' ')),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete actual return-list counts, prescribed source contracts and auxiliary factors have the same weighted limsup rate.",
        H("Actual complete counts and the auxiliary rate"),Blocks(
        Paragraph(Text("The variable weight N counts six times each m plus twenty times each r. The model fixes the high initial state XH or YH and the matching low initial state. Every supply uses the same execution list on both literal sources. External source order reverses the execution list while preserving the internal U, V and C labels. The original tails remain UC cubed followed by five and zeros, and VC cubed followed by zeros. Auxiliary bilateral padding serves only to count factors.")),
        Node("ActualDictionary",Mathematical(Equal(Dict(I("model"),I("d"),I("strict"),I("N")),Call("subtype",Lam("xs",Lists,
            And(Guard(I("model"),I("d"),I("strict"),I("xs")),Equal(Weight(I("xs")),I("N")))))),B("N",Nat)),
            "The complete lists satisfy the actual high-start guard trace and have exactly the indicated variable weight. Empty lists are included at weight zero.",DescribeRole.Definition),
        Node("actualCount",Mathematical(Equal(Count(I("model"),I("d"),I("strict"),I("N")),Call("NatCard",Dict(I("model"),I("d"),I("strict"),I("N")))),B("N",Nat)),
            "Only different complete lists are counted; errors and realizing positions are not extra choices.",DescribeRole.Definition),
        Node("actualLogRate",Mathematical(Equal(Log(I("model"),I("d"),I("strict"),I("N")),Normal(Count(I("model"),I("d"),I("strict"),I("N")),I("N"))),B("N",Nat)),
            "The max-one logarithm handles empty and unsupported weight fibres. Division at zero is the real division convention.",DescribeRole.Definition),
        Node("actualRate",Mathematical(Equal(Rate(I("model"),I("d"),I("strict")),Limsup(Lam("N",Nat,Log(I("model"),I("d"),I("strict"),I("N")))))),
            "This is the original sparse-weight upper limit, with N tending through all natural weights.",DescribeRole.Definition),
        Node("actualToFactor",OneCap(Call("hasType",Call("actualToFactor",I("model"),I("K"),I("d"),I("strict"),I("N")),
            Fn(Dict(I("model"),I("d"),I("strict"),I("N")),Factor(I("d"),I("N")))),B("N",Nat)),
            "The map retains exactly executionWord of the actual list. The original auxiliary lower padding proves that this word occurs in the same guard language, and the complete parser preserves its weight.",DescribeRole.Definition),
        Node("actual_to_factor_injective",OneCap(Call("Injective",Call("actualToFactor",I("model"),I("K"),I("d"),I("strict"),I("N"))),B("N",Nat)),
            "The complete c and u run parser recovers the actual positive return list from its execution word."),
        Node("actual_dictionary_bound",OneCap(And(Call("Finite",Dict(I("model"),I("d"),I("strict"),I("N"))),
            Le(Count(I("model"),I("d"),I("strict"),I("N")),FCount(I("d"),I("N"))),
            Le(Count(I("model"),I("d"),I("strict"),I("N")),Pow(F.D(3),Add(I("N"),F.D(1))))),B("N",Nat)),
            "The injection into the finite factor dictionary bounds both strict and weak complete-list counts uniformly at every weight."),
        Node("completedList",All(Equal(Completed,Cons(Call("return",Add(Field("m",I("R")),I("a")),F.D(1)),
            Cons(Call("return",Add(Field("m",I("first")),F.D(1)),Field("r",I("first"))),I("rest")))),B("R",Ret),B("a",Nat),B("first",Ret),B("rest",Lists)),
            "Leading u letters are absorbed into the low reset. One extra u is inserted after the first c run, even when this first return is low.",DescribeRole.Definition),
        Node("recoverFactor",All(And(
            Equal(Call("recoverFactor",I("R"),I("final"),Cons(I("reset"),Cons(I("extra"),I("rest")))),
                If(I("final"),Call("dropLast",Append(Rep(Sub(Field("m",I("reset")),Field("m",I("R"))),I("u")),
                    Append(Rep(Field("r",I("extra")),I("c")),Append(Rep(Sub(Field("m",I("extra")),F.D(1)),I("u")),EWord(I("rest")))))),
                    Append(Rep(Sub(Field("m",I("reset")),Field("m",I("R"))),I("u")),Append(Rep(Field("r",I("extra")),I("c")),Append(Rep(Sub(Field("m",I("extra")),F.D(1)),I("u")),EWord(I("rest"))))))),
            All(Imp(Lt(Call("length",I("xs")),F.D(2)),Equal(Call("recoverFactor",I("R"),I("final"),I("xs")),Call("nil",I("CuLetter")))),B("xs",Lists))),
            B("R",Ret),B("final",Bool),B("reset",Ret),B("extra",Ret),B("rest",Lists)),
            "Subtract the fixed number of reset u letters from the merged leading run. Remove the first-return extra u and, only for the final-c category, the last appended u. Lists shorter than two returns give the empty word.",DescribeRole.Definition),
        Node("same_reset_completion",Base(Completion()),
            "One finite low reset has output above both actual high starts and the threshold d. Enlarging a low first return retains strict actual supply, so the same reset supports weak-to-strict insertion and both factor-completion categories. The completion increases weight by CR plus six for final u and by CR plus twelve for final c. The two inserted u letters remain distinct when the first return is also the last."),
        Node("FactorClass",All(Equal(Call("FactorClass",I("K"),I("d"),I("N"),I("final")),Call("subtype",Lam("w",Factor(I("d"),I("N")),
            And(Call("member",I("c"),Val(I("w"))),Iff(LastC(Val(I("w"))),Equal(I("final"),I("true"))))))),B("K",Nat),B("d",Real),B("N",Nat),B("final",Bool)),
            "The two classes contain c and retain the exact final-letter distinction.",DescribeRole.Definition),
        Node("NoCFactor",All(Equal(Call("NoCFactor",I("K"),I("d"),I("N")),Call("subtype",Lam("w",Factor(I("d"),I("N")),
            Call("not",Call("member",I("c"),Val(I("w"))))))),B("K",Nat),B("d",Real),B("N",Nat)),
            "This is the separate class containing no c.",DescribeRole.Definition),
        Node("no_c_factor_card",All(Le(Call("NatCard",Call("NoCFactor",I("K"),I("d"),I("N"))),F.D(1)),B("K",Nat),B("d",Real),B("N",Nat)),
            "Such a word consists only of u. Its weight is six times its length, so a fixed weight determines at most one word, including zero and unsupported weights."),
        Node("same_reset_count_comparison",Base(CountComparison()),
            "Deleting the fixed reset recovers every weak list. For each final-letter class, recoverFactor is a left inverse of actual completion. The c-containing factors therefore inject into the two strict complete dictionaries at the literal shifted weights. The class without c contributes at most one."),
        Node("actual_log_rate_bounds",OneCap(And(All(Le(F.D(0),Log(I("model"),I("d"),I("strict"),I("N"))),B("N",Nat)),
            Bounded(Lam("N",Nat,Log(I("model"),I("d"),I("strict"),I("N")))))),
            "The max-one quotients are nonnegative, and their upper bounds are inherited from the actual factor injection."),
        Node("actual_fixed_shift_rate",OneCap(And(Bounded(Lam("N",Nat,Shifted(I("N")))),
            Equal(Limsup(Lam("N",Nat,Shifted(I("N")))),Rate(I("model"),I("d"),I("strict")))),B("C",Nat)),
            "Translation by a fixed natural weight preserves the upper limit. The changed denominator multiplies a bounded nonnegative sequence by (N plus C) divided by N, which tends to one. No positivity of the rate or support at every weight is required."),
        Node("actual_rates_equal",Base(All(Equal(Rate(I("src"),D,I("false")),Rate(I("dst"),D,I("true"))),B("src",Model),B("dst",Model))),
            "Both directions of reset insertion, together with strict inclusion in weak and the proved fixed-shift formula, identify both starts and flags."),
        Node("actual_auxiliary_rate_bridge",Base(All(Equal(Rate(I("model"),D,I("strict")),FRate(D)),B("model",Model),B("strict",Bool))),
            "The lower comparison is the actual-to-factor injection. For the upper comparison, the two shifted strict counts and one are bounded by three times their max-one maximum. The normalized extra logarithm tends to zero, and both shifted upper limits equal the strict actual rate."),
        Node("eta_b",All(Equal(Eta,Rate(I("original"),D,I("false"))),B("K",Nat),B("b",Real)),
            "The canonical value selects the weak original-start expression of definition 62.8. The rate bridge proves independence of this selection.",DescribeRole.Definition),
        Node("contractStrict",All(Equal(Flag,If(Equal(I("contract"),I("closed")),Call("boolNot",Call("apply",I("o"),F.D(0))),I("true"))),B("o",I("Ownership")),B("contract",I("Contract"))),
            "The high nearest endpoint is owned exactly when o at zero is true. Closed supply then uses weak guards; non-owned closed, strict and record-margin supply use strict guards.",DescribeRole.Definition),
        Node("ContractDictionary",All(Equal(CDict(I("N")),Call("subtype",Lam("xs",Lists,And(Supply(I("model"),I("contract"),I("xs")),Equal(Weight(I("xs")),I("N")))))),
            B("model",Model),B("o",I("Ownership")),B("b",Real),B("contract",I("Contract")),B("N",Nat)),
            "The predicate is the original ActualPairSupply: both prescribed sources share the same list and history, with all future errors zero and the literal original-tail future readouts.",DescribeRole.Definition),
        Node("contractCount",All(Equal(CCount(I("N")),Call("NatCard",CDict(I("N")))),B("model",Model),B("o",I("Ownership")),B("b",Real),B("contract",I("Contract")),B("N",Nat)),
            "The actual source contract counts distinct complete lists at the variable weight.",DescribeRole.Definition),
        Node("contractRate",All(Equal(CRate,Limsup(Lam("N",Nat,Normal(CCount(I("N")),I("N"))))),B("model",Model),B("o",I("Ownership")),B("b",Real),B("contract",I("Contract"))),
            "This uses the same max-one normalized logarithm as the complete-list rate.",DescribeRole.Definition),
        Node("contractDictionaryEquiv",Base(All(Call("hasType",Call("contractDictionaryEquiv",I("model"),I("o"),I("b"),I("contract"),I("N"),I("K")),
            Call("Equiv",CDict(I("N")),Dict(I("model"),D,Flag,I("N")))),B("model",Model),B("contract",I("Contract")),B("N",Nat))),
            "The exact original strict, record-margin and owned closed supply characterizations give an equivalence that fixes the execution list in both directions.",DescribeRole.Definition),
        Node("contract_count_correspondence",Base(All(And(Call("Finite",CDict(I("N"))),Equal(CCount(I("N")),Count(I("model"),D,Flag,I("N")))),
            B("model",Model),B("contract",I("Contract")),B("N",Nat))),
            "The actual contract dictionary is finite and has the corresponding strict-flag count. A weak count is never substituted for a non-owned closed endpoint."),
        Node("original_actual_count_rate_bridge",Base(And(Equal(FRate(D),Eta),
            All(Equal(Rate(I("model"),D,I("strict")),Eta),B("model",Model),B("strict",Bool)),
            All(Equal(CRate,Eta),B("model",Model),B("contract",I("Contract"))))),
            "The same auxiliary weightedFactorRate equals eta_b, every complete actual strict or weak rate for both starts, and every original actual source contract rate. This is a rate statement for the specified templates. It does not assert equality of their finite languages, a common positive margin for all lists, finite-memory rate convergence, or all-even asymptotics."))));
}
