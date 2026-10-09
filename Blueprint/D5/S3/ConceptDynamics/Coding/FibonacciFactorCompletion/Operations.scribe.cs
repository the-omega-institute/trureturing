using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class OperationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Operations.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula I(string name) => F.Id(name);
    private static Formula Returns => Call("List", I("Return"));
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);

    private static Formula OperationStorage()
    {
        Formula Fn(Formula a,Formula b) => Call("Function",a,b);
        Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
        Formula Ex(Formula a,params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[.. v],a);
        Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
        var c=I("Configuration");var nat=I("Nat");var action=I("action");var initial=I("initialConfiguration");
        var model=I("model");var o=I("o");var b=I("b");var contract=I("contract");var n=I("N");
        var record=Call("OperationRecord",o,b,contract);var enc=I("encoding");var cuts=I("cuts");
        var family=I("family");var x=I("x");var t=I("t");var xs=I("xs");var states=I("states");
        var xType=Call("ExactActualPairFamily",model,o,b,contract,n);
        var cut=Call("apply",cuts,x);var state=Call("state",cut);var output=Call("output",cut);
        var horizon=Add(Call("observationOffset",model),n);
        Formula Peak(Formula h) => Call("Peak",action,initial,record,enc,h);
        var cutSpec=All(And(Call("Cut",action,initial,Call("history",model,Call("val",x)),cut),
            All(Imp(Call("Cut",action,initial,Call("history",model,Call("val",x)),t),Equal(t,cut)),B("t",Call("Frame",c,I("Label")))),
            Equal(Call("acquired",cut),horizon),Equal(output,I("nil")),Call("ReachThrough",action,initial,record,horizon,state)),B("x",xType));
        var count=Call("NatCard",xType);var bound=I("B");
        var capacity=All(Imp(Call("le",Peak(horizon),Call("toWithTop",bound)),
            Call("le",count,Sub(Pow(D(2),Add(bound,D(1))),D(1)))),B("B",nat));
        var fixedCapacity=All(Imp(All(Equal(Call("length",Call("apply",enc,state)),bound),B("x",xType)),
            Call("le",count,Pow(D(2),bound))),B("B",nat));
        var stateSet=Ex(And(Equal(Call("card",states),count),All(Iff(Call("member",I("c"),states),
            Ex(Equal(Call("state",Call("apply",cuts,x)),I("c")),B("x",xType))),B("c",c))),B("states",Call("Finset",c)));
        var vertices=All(Imp(And(Call("OperationRecord",o,b,contract,I("a"),I("r")),
            Call("Trace",action,Call("full",I("r")),Call("frame",initial,D(0),I("nil")),t,I("vertices")),
            Call("le",Call("acquired",t),horizon),Call("member",I("c"),I("vertices"))),
            Call("le",Call("toWithTop",Call("length",Call("apply",enc,I("c")))),Peak(horizon))),
            B("a",Fn(nat,I("Label"))),B("r",Fn(nat,I("Color"))),B("t",Call("Frame",c,I("Label"))),
            B("vertices",Call("List",c)),B("c",c));
        var conclusion=Ex(And(All(Iff(Call("member",xs,family),And(Call("ActualPairSupply",model,o,b,contract,xs),
            Equal(Call("listWeight",xs),n))),B("xs",Returns)),Equal(Call("card",family),count),cutSpec,
            Call("Injective",Call("stateCutMap",cuts)),stateSet,capacity,fixedCapacity,
            Call("Monotone",Call("PeakFunction",action,initial,record,enc)),vertices),
            B("family",Call("Finset",Returns)),B("cuts",Fn(xType,Call("Frame",c,I("Label")))));
        var premises=And(Call("Processing",action,initial,record),Call("OperationSafety",action,initial,o,b,contract),
            Call("OperationLiveness",action,initial,o,b,contract),Call("InjOn",enc,Call("AllActualReachable",action,initial,record)));
        return Disp(All(Imp(premises,conclusion),B("Configuration",I("Type")),
            B("action",Fn(c,Call("Op",c,I("Color"),I("Label")))),B("initialConfiguration",c),B("model",I("Model")),
            B("o",I("Ownership")),B("b",I("Real")),B("contract",I("Contract")),B("N",nat),B("encoding",Fn(c,Call("List",I("Bool"))))));
    }
    private static Formula OperationStem()
    {
        Formula Fn(Formula a,Formula b) => Call("Function",a,b);
        Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
        Formula Ex(Formula a,params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[.. v],a);
        Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
        var c=I("Configuration");var zType=I("Z");var z=I("z");var nat=I("Nat");var action=I("action");var initial=I("initialConfiguration");
        var o=I("o");var b=I("b");var contract=I("contract");var n=I("n");var w=I("w");var k=Call("length",w);
        var alpha=I("alpha");var beta=I("beta");var high=I("highRecord");var low=I("lowRecord");
        Formula Source(Formula a,Formula q) => Call("apply",a,q);
        Formula At(Formula a,Formula q,Formula p) => Call("apply",Source(a,q),p);
        var actual=All(And(Call("OperationRecord",o,b,contract,Source(alpha,z),Source(high,z)),
            Call("OperationFiniteSource",Source(alpha,z)),Call("OperationRecord",o,b,contract,Source(beta,z),Source(low,z))),B("z",zType));
        var past=All(Imp(Call("lt",I("p"),n),Equal(At(high,z,I("p")),At(low,z,I("p")))),B("z",zType),B("p",nat));
        var future=All(Equal(At(high,z,Add(n,I("p"))),At(high,I("otherZ"),Add(n,I("p")))),B("z",zType),B("otherZ",zType),B("p",nat));
        var stems=All(Imp(Call("lt",I("i"),k),And(Equal(At(alpha,z,I("i")),Call("get",w,I("i"))),
            Equal(At(beta,z,I("i")),Call("get",w,I("i"))))),B("z",zType),B("i",nat));
        var difference=All(Call("notEqual",At(alpha,z,k),At(beta,z,k)),B("z",zType));
        var cuts=I("cuts");var states=I("states");var cut=Call("apply",cuts,z);var output=Call("output",cut);var state=Call("state",cut);
        var cutSpec=All(And(Call("Cut",action,initial,Call("front",Source(high,z),n),cut),Call("le",Call("length",output),k),
            Equal(output,Call("take",w,Call("length",output))),Call("IsPrefix",output,w)),B("z",zType));
        var membership=All(Iff(Call("member",I("c"),states),Ex(Equal(state,I("c")),B("z",zType))),B("c",c));
        var conclusion=Ex(And(cutSpec,Call("Injective",Call("jointCutMap",cuts)),membership,
            Call("le",Call("NatCard",zType),Mul(Call("card",states),Add(k,D(1))))),
            B("cuts",Fn(zType,Call("Frame",c,I("Label")))),B("states",Call("Finset",c)));
        var premises=And(Call("Finite",zType),Call("Processing",action,initial,Call("OperationRecord",o,b,contract)),
            Call("OperationSafety",action,initial,o,b,contract),Call("OperationLiveness",action,initial,o,b,contract),
            actual,past,future,stems,difference,Call("Injective",alpha));
        return Disp(All(Imp(premises,conclusion),B("Configuration",I("Type")),B("Z",I("Type")),
            B("action",Fn(c,Call("Op",c,I("Color"),I("Label")))),B("initialConfiguration",c),
            B("o",I("Ownership")),B("b",I("Real")),B("contract",I("Contract")),
            B("alpha",Fn(zType,Fn(nat,I("Label")))),B("beta",Fn(zType,Fn(nat,I("Label")))),
            B("highRecord",Fn(zType,Fn(nat,I("Color")))),B("lowRecord",Fn(zType,Fn(nat,I("Color")))),
            B("n",nat),B("w",Call("List",I("Label")))));
    }


    private static Formula Ex(Formula body,params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.Exists,[.. vars],body);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Fn(Formula a,Formula b) => Call("Function",a,b);
    private static Formula BudgetRange()
    {
        var scale=Mul(Pow(I("g"),D(2)),Pow(I("chi"),I("K")));
        var fixedState=Call("divide",Call("aSide",I("high")),Sub(D(1),Mul(I("rho"),Pow(I("chi"),I("K")))));
        return And(Call("le",D(2),I("K")),
            Call("lt",Sub(I("lam"),Mul(scale,Call("hSide",I("high")))),I("b")),
            Call("lt",I("b"),Sub(I("lam"),Mul(scale,fixedState))));
    }
    private static Formula Threshold => Call("divide",Call("divide",Sub(I("lam"),I("b")),Pow(I("g"),D(2))),Pow(I("chi"),I("K")));
    private static Formula WeakBook(Formula model,Formula n) => Call("WeakCodebook",I("K"),Threshold,model,n);
    private static Formula ResetCost => Add(D(2,0),Mul(D(6),Call("m",I("R"))));
    private static Formula BookLength => Add(I("N"),ResetCost);
    private static Formula EqualWeightCodebook()
    {
        var words=I("words");var xs=I("xs");var model=I("targetModel");var n=I("N");
        var weak=And(Call("GuardTrace",I("K"),Threshold,I("false"),I("high"),xs,Call("initial",I("high"),I("sourceModel"))),Equal(Call("listWeight",xs),n));
        var admissible=All(Imp(Call("member",xs,words),weak),B("xs",Returns));
        var joint=All(Imp(admissible,And(
            Call("ActualPairSupply",model,I("o"),Sub(I("b"),I("eps")),I("closed"),Call("resetConcatenation",I("R"),words)),
            All(Call("ActualPairSupply",model,I("o"),I("b"),I("contract"),Call("resetConcatenation",I("R"),words)),B("contract",I("Contract"))),
            Equal(Call("listWeight",Call("resetConcatenation",I("R"),words)),Mul(Call("length",words),BookLength)))),
            B("targetModel",I("Model")),B("words",Call("List",Returns)));
        var counts=All(Call("le",Pow(Call("NatCard",WeakBook(I("sourceModel"),n)),I("q")),
            Call("NatCard",Call("ExactActualPairFamily",model,I("o"),I("b"),I("contract"),Mul(I("q"),BookLength)))),
            B("targetModel",I("Model")),B("contract",I("Contract")),B("q",I("Nat")));
        var books=All(Imp(Call("lt",D(0),n),And(Call("Finite",WeakBook(I("sourceModel"),n)),
            Ex(And(Call("lt",D(0),I("eps")),Call("lt",D(0),BookLength),joint,counts),B("eps",I("Real"))))),
            B("sourceModel",I("Model")),B("N",I("Nat")));
        return Disp(All(Imp(BudgetRange(),Ex(And(Equal(Call("r",I("R")),D(1)),books),B("R",I("Return")))),
            B("o",I("Ownership")),B("b",I("Real")),B("K",I("Nat"))));
    }
    private static Formula OperationPremises(bool includeBudget = true)
    {
        var c=I("Configuration");var nat=I("Nat");var action=I("action");var init=I("initialConfiguration");
        var record=Call("OperationRecord",I("o"),I("b"),I("contract"));
        var r=I("recordInput");var source=I("address");var t=I("t");
        var initial=Call("frame",init,D(0),I("nil"));
        var safe=All(Imp(And(Call("apply",record,source,r),Call("Run",action,Call("full",r),initial,t),
            Call("lt",I("p"),Call("length",Call("output",t)))),Equal(Call("get",Call("output",t),I("p")),Call("apply",source,I("p")))),
            B("address",Fn(nat,I("Label"))),B("recordInput",Fn(nat,I("Color"))),B("t",Call("Frame",c,I("Label"))),B("p",nat));
        var live=All(Imp(And(Call("apply",record,source,r),Call("OperationFiniteSource",source)),
            Ex(And(Call("Run",action,Call("full",r),initial,t),Call("lt",I("p"),Call("length",Call("output",t)))),B("t",Call("Frame",c,I("Label"))))),
            B("address",Fn(nat,I("Label"))),B("recordInput",Fn(nat,I("Color"))),B("p",nat));
        var f=I("f");var outword=I("outword");var batch=I("batch");var q=I("q");
        var post=All(Imp(And(Call("apply",record,source,r),
            Call("Run",action,Call("full",r),initial,Call("frame",I("c"),q,outword)),
            Equal(Call("apply",action,I("c")),Call("acquire",f)),
            Equal(Call("apply",f,Call("apply",r,q)),Call("some",Call("pair",I("d"),batch)))),
            Ex(Call("Drain",action,Call("frame",I("d"),Add(q,D(1)),Call("append",outword,batch)),t),B("t",Call("Frame",c,I("Label"))))),
            B("address",Fn(nat,I("Label"))),B("recordInput",Fn(nat,I("Color"))),B("c",c),B("d",c),B("q",nat),
            B("outword",Call("List",I("Label"))),B("batch",Call("List",I("Label"))),
            B("f",Fn(I("Color"),Call("Option",Call("Product",c,Call("List",I("Label")))))));
        var faithful=Call("InjOn",I("encoding"),Call("AllActualReachable",action,init,record));
        return includeBudget ? And(BudgetRange(),safe,live,post,faithful) : And(safe,live,post,faithful);
    }
    private static Formula CompletePeak => Call("PeakFunction",I("action"),I("initialConfiguration"),
        Call("OperationRecord",I("o"),I("b"),I("contract")),I("encoding"));
    private static Formula PeakRatioLiminf => Call("liminfAtTop",Call("CompletePeakRatio",CompletePeak));
    private static Formula StorageTelescope(Formula body) => Disp(All(Imp(OperationPremises(),body),
        B("Configuration",I("Type")),B("action",Fn(I("Configuration"),Call("Op",I("Configuration"),I("Color"),I("Label")))),
        B("initialConfiguration",I("Configuration")),B("o",I("Ownership")),B("b",I("Real")),B("contract",I("Contract")),
        B("K",I("Nat")),B("encoding",Fn(I("Configuration"),Call("List",I("Bool"))))));
    private static Formula CodebookStorageBound()
    {
        var a=Call("NatCard",WeakBook(I("sourceModel"),I("N")));var delta=Call("observationOffset",I("model"));
        var horizon=I("H");var bound=I("B");var loga=Call("logb",D(2),Call("toReal",a));
        var floor=Call("toReal",Call("natDivide",Sub(horizon,delta),BookLength));
        var finite=All(Imp(And(Call("le",delta,horizon),Call("le",Call("apply",CompletePeak,horizon),Call("toWithTop",bound))),
            Call("le",Sub(Mul(floor,loga),D(1)),Call("toReal",bound))),B("H",I("Nat")),B("B",I("Nat")));
        var coefficient=Call("le",Call("ofReal",Call("divide",loga,Call("toReal",BookLength))),PeakRatioLiminf);
        return And(finite,coefficient);
    }
    private static Formula CodebookStorage()
    {
        var a=Call("NatCard",WeakBook(I("sourceModel"),I("N")));
        var books=All(Imp(Call("lt",D(0),I("N")),Imp(Call("le",D(1),a),
            All(CodebookStorageBound(),B("model",I("Model"))))),B("sourceModel",I("Model")),B("N",I("Nat")));
        return StorageTelescope(Ex(And(Equal(Call("r",I("R")),D(1)),books),B("R",I("Return"))));
    }
    private static Formula SuppliedCodebookStorage()
    {
        var a=Call("NatCard",WeakBook(I("sourceModel"),I("N")));
        var count=All(Call("le",Pow(a,I("q")),Call("NatCard",Call("ExactActualPairFamily",
            I("model"),I("o"),I("b"),I("contract"),Mul(I("q"),BookLength)))),B("q",I("Nat")));
        var sources=And(Call("lt",D(0),I("N")),Call("le",D(1),a),
            Call("ActualPairSupply",I("model"),I("o"),I("b"),I("contract"),I("nil")),count);
        return Disp(All(Imp(And(OperationPremises(false),sources),CodebookStorageBound()),
            B("Configuration",I("Type")),B("action",Fn(I("Configuration"),Call("Op",I("Configuration"),I("Color"),I("Label")))),
            B("initialConfiguration",I("Configuration")),B("o",I("Ownership")),B("b",I("Real")),B("contract",I("Contract")),
            B("K",I("Nat")),B("encoding",Fn(I("Configuration"),Call("List",I("Bool")))),
            B("R",I("Return")),B("sourceModel",I("Model")),B("model",I("Model")),B("N",I("Nat"))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-supplied-codebook-storage-liminf"),DeclarationHandle.Create(Prefix+"supplied_codebook_storage_liminf"),
                H("A supplied reset retains the all-horizon codebook bound"),StatementSource.FromAuthor(SuppliedCodebookStorage()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("R, sourceModel, target model and exact weight N are supplied parameters. The source premises are the empty-list ActualPairSupply and, for every q, the power of the full weak dictionary cardinal bounded by the cardinal of all actual supplied lists of weight q(N+20+6R.m). They assert actual source membership and count, never decoder capacity, a configuration injection or a storage lower bound. The primitive-operation capacity bound on those actual sources, followed by floor interpolation and the finite or infinite peak cases, gives the displayed lower-limit conjunction. Choosing the original reset and actual source book yields original_codebook_storage_liminf.")),
                    Paragraph(Text("An exact downstream application may use the same supplied FixedCodebook R and its unchanged actual field. Its positive fixed-codebook error converts the strict supply at b-eps to each original contract at b; literal reset concatenation and the existing equal-weight parser derive all-q counts. The original source labels, colors and guards, both templates with offsets 26/52, same-list high/low D sources, first labels 5/0, empty past output and high common future versus the low side's own future retain their meanings. Margins may depend on N. No equality between separately chosen existential resets is required.")),
                    Paragraph(Text("For the stated original color-record contract, Configuration contains the decoder's actual readable control, phase, persistent and temporary workspace, counters, input/output positions, clocks, timing and readable output-side storage. action follows its actual primitive instructions, retaining every charged intermediate state and actual finite ordered emission. Frame.acquired and Frame.output are proof-only bookkeeping and provide no machine input. Finite-prefix trace correspondence transports all-Omega safety, all-D per-position liveness including L0 padding, and finite processing. This is a source interpretation of the stated contract, without an independent physical-machine universality claim.")),
                    Paragraph(Text("The original prefix cost is the supremum over all actual reached configurations with acquisition count at most H. Reach inclusion gives monotonicity. Split an original top peak before choosing finite layouts: it remains top at all larger horizons and its ratio liminf is top. Otherwise actual complete binary layouts are faithful on actual reach, with harmless totalization elsewhere. Trace reflection and each reached layout's charged cost bound give operationalPeak(H)<=originalPeak(H) by indexed suprema. No uniform memory, state, support or processing bound and no free checkpoint lower bound are supplied. The necessary coefficient does not assert a uniform eta_b H-C loss or an attaining decoder."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-original-equal-weight-codebook"),DeclarationHandle.Create(Prefix+"original_equal_weight_codebook"),
                H("Full finite weak codebooks with one reset at every seam"),StatementSource.FromAuthor(EqualWeightCodebook()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("WeakCodebook(K,d,sourceModel,N) is the entire subtype of return lists xs with GuardTrace K d false high xs (initial high sourceModel) and listWeight xs=N. The single reset R is chosen before sourceModel and N. Its r is one and C_R=20+6R.m. resetConcatenation(R,[]) is []; resetConcatenation(R,xs::words) is (R::xs) appended to resetConcatenation(R,words). Each chosen word receives this same reset. For every N>0 the full subtype is finite. The positive eps may depend on N and sourceModel, but works for every finite joint choice, every target model and every number of seams. It supplies the actual paired sources at closed budget b-eps and hence all three contracts at b. Their fixed literal tails and zero-error futures are those of ActualPairSupply. The total weight is q(N+C_R).")),
                    Paragraph(Text("The reset state strictly exceeds either initial state. The affine difference over every word prefix is bounded below by (B-D)g^N; choosing eps below a fixed multiple of that gap makes each high guard strict at every seam. The exact positive weights recover equal-weight words from their cumulative cuts, even when their return-list lengths differ. Thus all q-tuples inject into actual lists and give at least NatCard(WeakCodebook)^q members. Empty and unsupported codebooks and q=0 are included. No common margin over all weights is asserted."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-original-codebook-storage-liminf"),DeclarationHandle.Create(Prefix+"original_codebook_storage_liminf"),
                H("All observation horizons force the exact codebook coefficient"),StatementSource.FromAuthor(CodebookStorage()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("AllActualReachable consists of configurations c for which ReachThrough(H,c) holds for some H. The supplied encoding is injective on this complete set. PeakFunction(H) is the WithTop Nat supremum of encoding lengths over all records and all primitive vertices through H. CompletePeakRatio(H) is ENat.toENNReal(PeakFunction(H))/(H:ENNReal), and liminfAtTop is its lower limit over natural observation horizons. Safety, positionwise D liveness and finite drains after actual acquisitions are expanded in the displayed premises; no independent startup premise is supplied. Actual empty-list high/low records have distinct first labels, so these contracts derive finite startup.")),
                    Paragraph(Text("For every fixed N>0 with a=NatCard(WeakCodebook)>=1, L=N+C_R is positive and Delta is the original 26 or anchored 52. The exhaustive actual-operation separation and full variable-length capacity yield a^q<=2^(B+1)-1 at Delta+qL. Monotonicity of the complete peak transfers this bound to q=floor((H-Delta)/L) for every H>=Delta. Thus q log2(a)-1<=B whenever the full peak is bounded by B. Floor interpolation has a fixed-codebook loss divided by H, which tends to zero. Infinite peaks are treated as top, without finite conversion. The resulting necessary lower-limit coefficient is exactly log2(a)/(N+C_R)."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-original-operation-decoder-storage"),
                DeclarationHandle.Create(Prefix+"original_operation_decoder_storage"), H("Actual primitive cuts and the complete encoding peak"),
                StatementSource.FromAuthor(OperationStorage()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("OperationOmega(a,x) is exactly the original legal supported affine path: path starts at G0, follows nextGuard on a, supports x at each position, and x(p)=branch(a(p),x(p+1)). OperationRecord(o,b,contract)(a,r) supplies that path and an original ErrorBound error with observe(o,x(p),err(p))=r(p) at every position. OperationFiniteSource is eventual L0. OperationSafety and OperationLiveness quantify every such original record and every finite primitive trace, with positionwise liveness on eventual L0 sources. Processing includes the real startup drain and actual post-acquisition drains, with no global termination on unreachable states.")),
                    Paragraph(Text("ExactActualPairFamily is the subtype of all return lists satisfying ActualPairSupply(model,o,b,contract) and listWeight=N, without sampling or weight monotonicity. The original anonymous45 finite-family construction is reused. Every cut is constructed from actual D liveness. Its high and low paired records share history(model,xs); the same retained primitive past trace embeds on the low record. Safety and the actual L5/L0 first difference force the output word to be empty. Equal original cut states replay the same literal high future; safety and positionwise D liveness recover equal addresses and the original source injection recovers the return lists. Cut uniqueness follows primitive determinism at input exhaustion.")),
                    Paragraph(Text("stateCutMap(cuts)(x) is state(cuts(x)). states is its finite image, whose cardinal is exactly NatCard of the exhaustive family. The history length is observationOffset(model)+N, namely 26+N for original and 52+N for anchored. AllActualReachable means configurations in ReachThrough(H) for some H. The supplied original complete encoding is injective on that set. PeakFunction is H mapped to the full WithTop Nat encoding-length supremum over every actual record and primitive intermediate state. A finite peak bound B yields at most 2^(B+1)-1 variable-length codes. Fixed complete width B at the selected states yields at most 2^B codes. Infinite peaks and empty or unsupported exact-weight families remain included. Every trace vertex in the horizon is bounded by this full peak.")),
                    Paragraph(Text("This result is for the explicit primitive operation presentation. It proves neither universal representation of every prose decoder nor the source initialization and endpoint correspondence. The equal-weight codebook and complete-storage lower-limit results provide the additional necessary coefficient argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-original-operation-common-stem"),
                DeclarationHandle.Create(Prefix+"original_operation_common_stem"), H("One fixed actual stem gives the original prefix factor"),
                StatementSource.FromAuthor(OperationStem()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite supplied family has actual alpha records in eventual L0 and actual beta records in Omega, using precisely OperationRecord and all original error contracts and endpoint flags. Each high and low record shares the same n acquired colors for its family member. The high unread future is the same across members; the low future may differ. The single word w is fixed independently of the family member. Both actual addresses agree with w before its length and differ at that position; sourceInjection concerns alpha addresses only and is a source-side hypothesis.")),
                    Paragraph(Text("Actual high-side liveness constructs each cut, and primitive past transfer supplies the beta run without assuming progress on all Omega records. Safety at the first disagreement bounds old output length by length(w); safety before it gives output=take(w,length(output)) and prefix membership. Equal cut state and old word then permit unread-suffix replay, forcing equal alpha addresses and equal family members. jointCutMap is the external pair of cut state and cumulative old word. Prefix length injects the possible words into Fin(length(w)+1). Counting the finite state image times that many prefix tags gives NatCard(Z) at most card(states)*(length(w)+1). The old word is never readable storage. No prefix or joint decoder injection is assumed.")),
                    Paragraph(Text("This theorem requires actual source-side witnesses and preserves their fixed-stem and common-future scope. The original39.7 construction supplying those witnesses is not newly formalized here. It is not a standalone product-cardinality result and does not change the retained k0 source family."))), DescribeRole.Theorem))));
}
