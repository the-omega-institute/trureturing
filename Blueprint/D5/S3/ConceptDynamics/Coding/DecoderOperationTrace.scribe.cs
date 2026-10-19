using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;
internal sealed class DecoderOperationTraceDocument : IScribeDocumentDefinition
{
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula body, params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,[.. vars],body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.Exists,[.. vars],body);
    private static Formula And(params Formula[] p)
    {
        var r=p[^1]; for(var j=p.Length-2;j>=0;j--) r=new Formula.Logic(p[j],FormulaLogicOperator.And,r); return r;
    }
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Fn(Formula a,Formula b) => Call("Function",a,b);
    private static Formula List(Formula a) => Call("List",a);
    private static Formula Nat => I("Nat");
    private static Formula State(Formula s) => Call("state",s);
    private static Formula Acquired(Formula s) => Call("acquired",s);
    private static Formula Output(Formula s) => Call("output",s);
    private static Formula Add(Formula a,Formula b) => Call("add",a,b);
    private static Formula Append(Formula a,Formula b) => Call("append",a,b);
    private static Formula Frame(Formula c,Formula q,Formula o) => Call("frame",c,q,o);
    private static Formula Initial => Frame(I("initial"),D(0),I("nil"));
    private static Formula RecordType => Fn(Fn(Nat,I("O")),Fn(Fn(Nat,I("I")),I("Prop")));
    private static Formula FrameType => Call("Frame",I("C"),I("O"));
    private static Formula ActionType => Fn(I("C"),Call("Op",I("C"),I("I"),I("O")));
    private static Formula Run(Formula r,Formula s,Formula t) => Call("Run",I("action"),Call("full",r),s,t);
    private static Formula Trace(Formula r,Formula s,Formula t,Formula v) => Call("Trace",I("action"),Call("full",r),s,t,v);
    private static Formula Safety => Call("Safety",I("action"),I("initial"),I("Record"));
    private static Formula Live => Call("Liveness",I("action"),I("initial"),I("Record"),I("InD"));
    private static Formula Replay()
    {
        var s=I("s");var t=I("t");var m=I("m");var w=I("w");var v=I("vertices");
        var suffix=All(Equal(Call("apply",I("r"),Add(Acquired(s),I("j"))),Call("apply",I("otherInput"),Add(I("otherOffset"),I("j")))),B("j",Nat));
        var continuation=All(Imp(suffix,Trace(I("otherInput"),Frame(State(s),I("otherOffset"),I("otherOutput")),
            Frame(State(t),Add(I("otherOffset"),m),Append(I("otherOutput"),w)),v)),
            B("otherInput",Fn(Nat,I("I"))),B("otherOffset",Nat),B("otherOutput",List(I("O"))));
        return Disp(All(Imp(Trace(I("r"),s,t,v),Ex(And(Equal(Acquired(t),Add(Acquired(s),m)),
            Equal(Output(t),Append(Output(s),w)),continuation),B("m",Nat),B("w",List(I("O"))))),
            B("C",I("Type")),B("I",I("Type")),B("O",I("Type")),B("action",ActionType),
            B("r",Fn(Nat,I("I"))),B("s",FrameType),B("t",FrameType),B("vertices",List(I("C")))));
    }
    private static Formula Addresses()
    {
        var s=I("s");var t=I("otherCut");
        var future=All(Equal(Call("apply",I("r"),Add(Acquired(s),I("j"))),
            Call("apply",I("otherInput"),Add(Acquired(t),I("j")))),B("j",Nat));
        return Disp(All(Imp(And(Safety,Live,Call("Record",I("a"),I("r")),Call("Record",I("b"),I("otherInput")),
            Call("InD",I("a")),Run(I("r"),Initial,s),Run(I("otherInput"),Initial,t),
            Equal(State(s),State(t)),Equal(Output(s),Output(t)),future),Equal(I("a"),I("b"))),
            B("C",I("Type")),B("I",I("Type")),B("O",I("Type")),B("action",ActionType),B("initial",I("C")),
            B("Record",RecordType),B("InD",Fn(Fn(Nat,I("O")),I("Prop"))),
            B("a",Fn(Nat,I("O"))),B("b",Fn(Nat,I("O"))),B("r",Fn(Nat,I("I"))),B("otherInput",Fn(Nat,I("I"))),
            B("s",FrameType),B("otherCut",FrameType)));
    }
    private static Formula Vertices()
    {
        var code=Call("apply",I("encoding"),I("c"));
        return Disp(All(Imp(And(Call("Record",I("a"),I("r")),Trace(I("r"),Initial,I("t"),I("vertices")),
            Call("le",Acquired(I("t")),I("H")),Call("member",I("c"),I("vertices"))),
            Call("le",Call("toWithTop",Call("length",code)),Call("Peak",I("action"),I("initial"),I("Record"),I("encoding"),I("H")))),
            B("C",I("Type")),B("I",I("Type")),B("O",I("Type")),B("action",ActionType),B("initial",I("C")),
            B("Record",RecordType),B("encoding",Fn(I("C"),List(I("Bool")))),B("H",Nat),
            B("a",Fn(Nat,I("O"))),B("r",Fn(Nat,I("I"))),B("t",FrameType),B("vertices",List(I("C"))),B("c",I("C"))));
    }

    private const string LiteralPrefix = "D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.";
    private static Formula.BoundVariable LiteralB(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula LiteralAll(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula LiteralImp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula LiteralAnd(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula LiteralI(string name) => F.Id(name);
    private static Formula LiteralWords => Call("List", LiteralI("Label"));
    private static Formula LiteralReturns => Call("List", LiteralI("Return"));
    private static Formula LiteralLen(Formula word) => Call("length", word);
    private static Formula LiteralCoord(Formula word, Formula position) => Call("coordinate", word, position);
    private static Formula LiteralComp(Formula word, Formula point) => Call("compose", word, point);
    private static Formula LiteralAdd(Formula a, Formula b) => Call("add", a, b);
    private static Formula LiteralSub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula LiteralMul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula LiteralPow(Formula a, Formula b) => Call("power", a, b);
    private static Formula LiteralAppend(Formula a, Formula b) => Call("append", a, b);

    private static Formula LiteralGeometry()
    {
        var w = LiteralI("w"); var v = LiteralI("v"); var z = LiteralI("z");
        var s = LiteralI("s"); var e = LiteralI("e"); var p = LiteralI("p");
        var left = LiteralI("left"); var block = LiteralI("B"); var right = LiteralI("right");
        var x = LiteralI("x"); var y = LiteralI("y");
        return Disp(LiteralAnd(
            LiteralAll(LiteralImp(LiteralAnd(Call("LegalWord", s, e, w), Call("InSupport", e, z)),
                    Call("InSupport", s, LiteralComp(w, z))),
                LiteralB("s", LiteralI("Guard")), LiteralB("e", LiteralI("Guard")), LiteralB("w", LiteralWords), LiteralB("z", LiteralI("Real"))),
            LiteralAll(LiteralImp(Call("le", p, LiteralLen(block)), Equal(
                    LiteralCoord(LiteralAppend(LiteralAppend(left, block), right), LiteralAdd(LiteralLen(left), p)),
                    LiteralAdd(LiteralComp(Call("drop", block, p), LiteralI("c0")),
                        LiteralMul(LiteralPow(Call("negate", LiteralI("g")), LiteralSub(LiteralLen(block), p)),
                            LiteralSub(LiteralCoord(right, D(0)), LiteralI("c0")))))),
                LiteralB("left", LiteralWords), LiteralB("B", LiteralWords), LiteralB("right", LiteralWords), LiteralB("p", LiteralI("Nat"))),
            LiteralAll(Equal(LiteralCoord(LiteralAppend(w, Call("replicate", LiteralI("n"), LiteralI("L0"))), p), LiteralCoord(w, p)),
                LiteralB("w", LiteralWords), LiteralB("n", LiteralI("Nat")), LiteralB("p", LiteralI("Nat"))),
            LiteralAll(Equal(LiteralComp(w, LiteralAdd(x, y)),
                    LiteralAdd(LiteralComp(w, x), LiteralMul(LiteralPow(Call("negate", LiteralI("g")), LiteralLen(w)), y))),
                LiteralB("w", LiteralWords), LiteralB("x", LiteralI("Real")), LiteralB("y", LiteralI("Real"))),
            LiteralAll(Equal(LiteralComp(LiteralAppend(w, v), z), LiteralComp(w, LiteralComp(v, z))),
                LiteralB("w", LiteralWords), LiteralB("v", LiteralWords), LiteralB("z", LiteralI("Real")))));
    }

    private static Formula LiteralReconstruction()
    {
        var j = LiteralI("j"); var model = LiteralI("model"); var xs = LiteralI("execution");
        var p = LiteralI("p"); var state = LiteralI("D");
        var prefix = Call("observedPrefix", j, model, xs);
        var full = Call("sourcePrefix", j, model, xs);
        var tail = Call("tailPrefix", j);
        var external = Call("externalWord", j, xs);
        Formula Signed(Formula value) => LiteralAdd(LiteralI("c0"), LiteralMul(Call("sign", j), value));
        var paidLength = LiteralAdd(Call("observationOffset", model), Call("listWeight", xs));
        return Disp(LiteralAll(LiteralAnd(
            Call("LegalWord", LiteralI("G0"), LiteralI("G0"), full),
            LiteralAll(Equal(Call("source", j, model, xs, LiteralAdd(LiteralLen(prefix), p)), Call("address", tail, p)),
                LiteralB("p", LiteralI("Nat"))),
            LiteralAll(Equal(LiteralCoord(full, LiteralAdd(LiteralLen(prefix), p)), LiteralCoord(tail, p)), LiteralB("p", LiteralI("Nat"))),
            Equal(LiteralCoord(LiteralAppend(LiteralAppend(external, Call("anchor", j, model)), tail), D(0)),
                Signed(Call("execute", j, xs, Call("initial", j, model)))),
            Equal(LiteralLen(prefix), paidLength), Equal(LiteralLen(Call("history", model, xs)), paidLength),
            LiteralAll(Equal(LiteralComp(LiteralI("C"), Signed(state)), Signed(LiteralMul(LiteralI("chi"), state))), LiteralB("D", LiteralI("Real"))),
            LiteralAll(Equal(LiteralComp(Call("block", j), Signed(state)),
                Signed(LiteralAdd(Call("aSide", j), LiteralMul(LiteralI("rho"), state)))), LiteralB("D", LiteralI("Real"))),
            LiteralAll(Equal(LiteralComp(Call("returnWord", j, LiteralI("a")), Signed(state)),
                Signed(Call("returnMap", j, LiteralI("a"), state))), LiteralB("a", LiteralI("Return")), LiteralB("D", LiteralI("Real"))),
            LiteralAll(Equal(LiteralComp(Call("externalWord", j, LiteralI("xs")), Signed(state)),
                Signed(Call("execute", j, LiteralI("xs"), state))), LiteralB("xs", LiteralReturns), LiteralB("D", LiteralI("Real"))),
            Equal(LiteralComp(tail, D(0)), Signed(Call("xSide", j)))),
            LiteralB("j", LiteralI("Side")), LiteralB("model", LiteralI("Model")), LiteralB("execution", LiteralReturns)));
    }

    private static Formula LiteralPathLaw()
    {
        var path = LiteralI("path"); var p = LiteralI("p"); var w = LiteralI("w");
        Formula At(Formula n) => Call("apply", path, n);
        return Disp(LiteralAll(LiteralImp(Call("LegalWord", LiteralI("s"), LiteralI("e"), w),
            new Formula.BindMany(FormulaQuantifier.Exists,
                [LiteralB("path", Call("Function", LiteralI("Nat"), LiteralI("Guard")))], LiteralAnd(
                    Equal(At(D(0)), LiteralI("s")),
                    LiteralAll(Equal(Call("nextGuard", At(p), Call("address", w, p)),
                        Call("some", At(LiteralAdd(p, D(1))))), LiteralB("p", LiteralI("Nat"))),
                    LiteralAll(Call("InSupport", At(p), LiteralCoord(w, p)), LiteralB("p", LiteralI("Nat"))),
                    LiteralAll(Equal(LiteralCoord(w, p), Call("branch", Call("address", w, p),
                        LiteralCoord(w, LiteralAdd(p, D(1))))), LiteralB("p", LiteralI("Nat")))))),
            LiteralB("s", LiteralI("Guard")), LiteralB("e", LiteralI("Guard")), LiteralB("w", LiteralWords)));
    }

    private static Formula LiteralSlotLaw()
    {
        var o = LiteralI("o"); var b = LiteralI("b"); var j = LiteralI("j"); var state = LiteralI("D"); var z = LiteralI("z");
        Formula Supply(bool strict) => Call("BlockSupply", o, b, LiteralI(strict ? "true" : "false"),
            Call("block", j), LiteralI("colorsD"), LiteralAdd(LiteralI("c0"), LiteralMul(Call("sign", j), state)));
        var cost = LiteralSub(LiteralI("lam"), LiteralMul(LiteralPow(LiteralI("g"), D(2)), state));
        var domain = LiteralAnd(Call("lt", D(0), state), Call("le", state, Call("eSide", j)));
        var owned = new Formula.Logic(
            LiteralAnd(Equal(j, LiteralI("high")), Equal(Call("apply", o, D(0)), LiteralI("true"))),
            FormulaLogicOperator.Or,
            LiteralAnd(Equal(j, LiteralI("low")), Equal(Call("apply", o, D(1)), LiteralI("false"))));
        var closed = new Formula.Logic(Call("lt", cost, b), FormulaLogicOperator.Or,
            LiteralAnd(Equal(cost, b), owned));
        return Disp(LiteralAll(LiteralImp(Call("lt", LiteralSub(LiteralI("lam"), LiteralI("rho")), b), LiteralAnd(
            LiteralAll(LiteralImp(domain, new Formula.Logic(Supply(true), FormulaLogicOperator.Iff,
                Call("lt", cost, b))), LiteralB("j", LiteralI("Side")), LiteralB("D", LiteralI("Real"))),
            LiteralAll(LiteralImp(domain, new Formula.Logic(Supply(false), FormulaLogicOperator.Iff, closed)),
                LiteralB("j", LiteralI("Side")), LiteralB("D", LiteralI("Real"))),
            LiteralAll(LiteralImp(LiteralAnd(Call("le", D(0), z), Call("le", z, LiteralI("T2"))),
                Call("BlockSupply", o, b, LiteralI("true"), LiteralI("C"), LiteralI("colorsE"), z)),
                LiteralB("z", LiteralI("Real"))))), LiteralB("o", LiteralI("Ownership")), LiteralB("b", LiteralI("Real"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite actual operation traces preserve original readable states, emitted batches and acquisition boundaries.",
        H("Primitive decoder operations"),Blocks(
            Paragraph(Text("DecoderStartup supplies initial_drain_of_acquired_run and processing_of_safe_live_pair with their canonical statements.")),
            Paragraph(Text("A finite Run whose acquired count is positive contains a first acquisition. Its preceding retained prefix consists solely of internal operations and ends at the actual acquire state. Transfer to the empty available input gives a Drain from physical initialization. Every prefix vertex is retained; neither global computation bounds nor termination on unreachable states are required.")),
            Paragraph(Text("Safety and Liveness have exactly the all-Record finite-run and positionwise InD meanings displayed above. The two supplied actual records have different first source labels; only the first needs InD liveness. Its live first output cannot occur with zero acquisitions, since the same internal prefix transfers to the competitor and safety would equate their first labels. The acquired run therefore supplies finite startup. Processing then follows from that derived drain and the displayed drains after every actual successful acquisition. Post-acquisition finiteness is not inferred from safety alone. Original complete-readable-state and instruction correspondence remains a separate semantic assessment.")),

            Describe.Lean(DescribeId.Create("decoder-operation-trace-replay"),DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/DecoderReplay.trace_replay"),
                H("Unread suffix replay with independent old output"),StatementSource.FromAuthor(Replay()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Op has internal(next,batch), acquire(input to Option(next,batch)), and stopped. Step has only the two original internal and successful available acquisition rules. Frame consists of the original readable state and external acquired count and output word. action reads only the state. Trace retains its entire state vertex list and every finite edge batch. full(r)(q)=some(r(q)). Replay preserves that vertex list exactly, accumulates the actual acquisition and output increments, and changes neither state identity nor batches. Offset and old-output changes are external bookkeeping. Partial acquisition and unreachable loops remain allowed."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decoder-operation-actual-address-equality"),DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/DecoderReplay.actual_address_eq"),
                H("Live actual addresses agree after equal-state replay"),StatementSource.FromAuthor(Addresses()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Safety means that on every Record every emitted position in every finite primitive run equals its source address. Liveness is positionwise and restricted to InD. Equal cut states, equal cumulative words and one equal unread suffix imply address equality: choose a liveness witness beyond both the requested position and old output, compare actual paths, replay the continuation, and apply safety on both records. No replay or joint injection is a premise."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decoder-operation-peak-trace-bound"),DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/DecoderPeak.peak_trace_bound"),
                H("All readable vertices belong to the complete horizon peak"),StatementSource.FromAuthor(Vertices()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ReachThrough(H,c) means some Record has a finite primitive run from physical initialization ending at c with acquired count at most H. Peak is the WithTop Nat supremum of the lengths of the supplied original encodings over all such states. Every trace vertex has its actual prefix run, whose acquired count is no greater than the final count. Initialization, transient workspaces, acquisition states and completed endpoints are included. Infinite peaks are retained. The encoding and its original cost are supplied rather than replaced; no equality with a maximum over chosen cut states is asserted."))),DescribeRole.Theorem),
            Paragraph(Text("Literal Fibonacci sources and occurrence coordinates")),
            Paragraph(Text("The five-label affine source uses its original legal guards, endpoint flags, literal blocks and eventually-empty tails. Each departure coordinate belongs to one complete suffix of that source.")),
            Describe.Lean(DescribeId.Create("fib-literal-source-geometry"),
                DeclarationHandle.Create(LiteralPrefix + "literal_source_geometry"), H("One coordinate per occurrence"),
                StatementSource.FromAuthor(LiteralGeometry()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction over the literal word proves support preservation and its affine suffix law. Extending the finite cutoff by empty labels leaves every coordinate unchanged. The displacement in an occurrence formula is the coordinate of the actual complete right suffix minus the fixed center."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-paired-source-reconstruction"),
                DeclarationHandle.Create(LiteralPrefix + "paired_source_reconstruction"), H("Reconstruct both prescribed sources"),
                StatementSource.FromAuthor(LiteralReconstruction()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite block calculation uses every original cycle label. Induction reconstructs the reversed execution list without reversing block letters. Both templates have legal seams, the exact original tail at the unobserved terminal, the actual scalar return action, and observation lengths 26 plus the variable weight or 52 plus that weight."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-literal-address-path"),
                DeclarationHandle.Create(LiteralPrefix + "literal_address_path"), H("The complete literal departure path"),
                StatementSource.FromAuthor(LiteralPathLaw()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induction constructs a guard itinerary from the legal prefix. At every departure position, including the eventual empty tail, the coordinate lies in that guard's support and satisfies the original label branch recurrence."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application to every original block departure slot.")),
            Paragraph(Math(LiteralSlotLaw())),
            Paragraph(Text("This is an application of the existing affine and order results inside StrictSupply.actual_strict_cost_supply and ClosedSupply.actual_closed_record_supply. The ownership map o : Fin 5 -> Bool is arbitrary, as is the real budget b subject only to lam - rho < b. Both sides have sign high = 1 and sign low = -1. For every real displacement 0 < D <= eSide j, the strict six-slot U/V supply is equivalent to lam - g^2 D < b. The closed supply is equivalent to that strict inequality or exact equality together with high o 0 = true or low o 1 = false. These are per-occurrence error existentials, not a common error for a whole block. For every real 0 <= z <= T2, all twenty C/colorsE departures have their own error of magnitude strictly below b.")),
            Paragraph(Text("The parameters are t = (sqrt 5 - 1)/2, g = 2t - 1, phi = 1 + t, T2 = 1 - t, lam = T2/10, c0 = 2t/5, rho = g^6 and chi = g^20. The bounds g^2 + 4g = 1, 4/17 < g < 17/72, 59/250 < g and g < 1/4 follow by normalization from Real.sq_sqrt and Real.sqrt_nonneg at 5. The six-cell cuts in order are -1, -T2-lam, g-3lam, t-5lam, 2t-7lam, 2t+lam and phi. Clipping is max(-1,min(phi,x+error)); readout at each interior cut uses its own ownership bit to choose the adjacent color. On open cell interiors, ownership has no effect.")),
            Paragraph(Text("The actual literal words are U = [L5,L0,L3,L0,L3,L3], V = [L0,L3,L3,L5,L0,L3], and C = [L5,L5,L3,L2,L2,L0,L3,L3,L3,L25,L5,L0,L0,L2,L2,L25,L3,L3,L0,L5]. Their color lists are colorsD = [2,1,0,2,1,0] and colorsE = [2,3,0,3,4,2,0,1,0,5,2,1,1,3,3,5,0,0,1,2]. The suffix is dropped at the actual position p before composing; it is never a left prefix or a reversed block.")),
            Paragraph(Text("At input c0 the U suffix coordinates for p = 0,...,5 are (-257+1096g)/5, (-121+519g)/10, (-35+121g)/10, -3/5+3g, (-3+3g)/5, and (-7+g)/10. The V suffix coordinates are (-342+1451g)/5, (-83+342g)/5, (-45+161g)/10, -3/5+4g, (-1+11g)/10, and (-7+g)/10. Each table ends at coordinate c0 at p = 6. The branch recurrence at each of these finitely many positions is algebraic normalization. Nat.decreasingInduction' with List.drop_eq_getElem_cons and List.drop_eq_nil_of_le transports this table along the suffix; it adds no numerical assumption.")),
            Paragraph(Text("The affine clause of literal_source_geometry gives compose(w.drop p,z) - compose(w.drop p,c0) = (-g)^(length(w)-p)(z-c0). The bound |z-c0| <= 2/5 gives magnitude at most (1/4)^(length(w)-p) 2/5 by pow_le_pow_left₀ and mul_le_mul. For U/V, every nonactive p != 4 is strictly attainable: exists_between chooses y between max(cut i,x-b) and min(cut(i+1),x+b), and error = y-x has |error| < b and clips to the required open-cell point. At p = 4 the coordinate is cut 1 - lam + g^2 D on the high side and cut 2 + lam - g^2 D on the low side. Color 1 requires a point between these two cuts. Thus strict feasibility gives exactly the stated cost inequality. At equality in the closed contract the errors are b on high and -b on low, and the endpoint readout requires precisely o 0 = true or o 1 = false.")),
            Paragraph(Text("For C, write q_p = compose(C.drop p,c0). Every original occurrence is covered by the following color and coordinate pairs: p0: (2,(1+g)/5); p1: (3,(5+3g)/10); p2: (0,-4/5); p3: (3,(7+3g)/10); p4: (4,(9+3g)/10); p5: (2,(1+g)/10); p6: (0,(-5-g)/10); p7: (1,-2/5); p8: (0,(-9-g)/10); p9: (5,(6+2g)/5); p10: (2,(3+3g)/10); p11: (1,g/5); p12: (1,-1/5); p13: (3,(4+g)/5); p14: (3,(3+g)/5); p15: (5,(7+2g)/5); p16: (0,(-5+g)/10); p17: (0,-3/5); p18: (1,(-1+g)/10); p19: (2,(3+g)/10). The p20 suffix is empty and has coordinate c0. Every displayed q_p lies strictly inside the required color cell by the same cut and g bounds.")),
            Paragraph(Text("For each C occurrence p < 19, choose its own error q_p - compose(C.drop p,z). Its magnitude is at most (1/4)^(20-p) 2/5 <= 1/40 < b, using pow_le_pow_of_le_one and lam - rho < b; the corrected point is exactly q_p. At p = 19 choose error zero: throughout the full closed input interval [0,T2], the one-label suffix branch L5 z lies strictly between cut 2 and cut 3. These witnesses include both input endpoints and all twenty original positions. StrictSupply uses them at the actual input c0 + sign j chi^n D of each repeated C block. ClosedSupply uses the same strict witnesses and weakens only |error| < b to |error| <= b. The same-parameter bounds 0 < chi^n D < hSide j < eSide j and the actual interval domain are discharged in those proofs.")),
            Paragraph(Text("The source displacements are h_high = (39-6g)/380, h_low = (46+31g)/380, e_high = T2-c0, e_low = c0, a_j = (1-rho)h_j, x_j = a_j + rho chi^3 e_j and y_j = a_j + rho chi x_j. The initial displacement is x_j in the original model and y_j in the anchored model. The operational application retains every positive Return(m,r), with m > 0 and r > 0: returnWord is m copies of block j followed by r copies of C, returnColors has the corresponding replicated colors, and returnMap j a D = hSide j - rho^m(hSide j - chi^r D). External words group the reversed execution list while preserving each block's letters. The observed prefix is stem j ++ externalWord j execution ++ anchor j model, with stem = block j ++ C and anchor empty in the original model or stem in the anchored model. The tail is block j ++ C repeated three times ++ [L5,L0] on high or ++ [L0] on low, then the address defaults to L0 forever. The history is colorsD ++ colorsE ++ the flattened reversed returnColors, followed by no anchor colors or by colorsD ++ colorsE respectively. Both the observed and history lengths are exactly 26 or 52 plus sum(6m+20r), as supplied by paired_source_reconstruction.")),
            Paragraph(Text("ActualPairSupply uses one error function for each side of the prescribed source, with the complete-right-suffix coordinate at every history occurrence. The strict, closed and recordMargin contracts respectively require every |err p| < b, every |err p| <= b, or a single positive eps with every |err p| <= b-eps. At every p at or beyond the history length the error is zero, and all later readouts equal the actual tail readouts at zero error. The source reconstruction, literal_source_geometry and literal_address_path preserve the actual returns, legality, guards and zero-tail coordinates. The consumer proofs assemble the local errors through the actual words and history, without adding a premise or changing either model. These exact mathematical applications assert no physical decoder realization, resource optimum or literature novelty. The block feasibility formulas alone do not establish whole-record supply, cap/guard equivalences or asymptotic rates; those remain the conclusions of their actual supply, operation, storage and rate consumers.")),
            Paragraph(Text("ActualPairSupply is independently defined through clipped readout, error bounds, the prescribed history and zero-error futures. The declarations here reconstruct the literal sources; the block applications above are used inside the actual supply proofs. Whole-record supply is supplied separately by StrictSupply.actual_strict_record_supply and ClosedSupply.actual_closed_record_supply. StrictSupply.uniform_guard_trace_iff_split and exact_control_iff_split give their stated cap and guard conditions. Completion.auxiliary_factor_upper_completion and actual_source_address_injection provide the actual factor completion and literal-source separation. The exact original client anonymous37 assembles the every-weight list/history/source cardinalities and their rate equalities for both models, both contracts and offsets 26 and 52. Full auxiliary62.18 nesting, intersection and asymptotics, the interior spectral root, canonical containing paths and the compliant decoder33.13 optimum remain outside these local source laws.")))));
}
