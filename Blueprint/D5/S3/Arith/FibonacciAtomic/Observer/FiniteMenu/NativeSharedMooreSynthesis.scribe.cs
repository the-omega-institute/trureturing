using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu;
internal sealed class NativeSharedMooreSynthesisDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeSharedMooreSynthesis.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared finite Moore tables preserve the export, total installed state and invocation budgets on every actual predecessor fiber.",
        H("Shared Moore Transfer and Finite Synthesis"), Blocks(
            Paragraph(Text("Fix a finite prefix-free cut P and a complete current row C with a nonempty actual image fiber, represented by an arbitrary reference origin. In the formulas, rho denotes substitution, fill(C,v) denotes evaluateRow(extend C v.val.val,C), and nativeStep(M,t)(s) is M.next(s,readout(M.addr(s),t)). Value arguments of types and DeepValues are coerced to their underlying class functions. BoundedCandidateType(C) is the dependent sum of Candidate(C,a,b) over all natural a,b; Running(A), Halts(A), States(A), table(A) and color(A) are its actual components. The domain consists of every finite origin u with canonicalRow P (substitution u) = C. ImageValues C are the actually acquired injective class values; the original row-fiber correspondence retains the complete exterior, every repeated class occurrence, every different-class disequality and every blocked cut member. There is no source-size, hidden-depth or intrinsic-rank restriction. The attained chart is NativeClassRootSimulation.Chart C, enumerated by NativeFiniteRootMinimax.chartList. Its entire predecessor target is NativeFullRootFeasibility.target, computed by computedTarget. The public finite_root_minimax theorem supplies both exact interfaces directly.")),
            Paragraph(Text("A native table is the existing NativeSixSourceMoore.Controller Q H, with disjoint running and halting carriers. Each running state has one fixed finite literal address and four reply transitions into Q plus H. Each halt stores its complete LiteralRow output. All installed states count, including unused states and different halts with equal outputs. The normalized exported value is the initial state itself, and inclusion is its recoverable entry map. For an original actual finite export sigma and lawful entry iota, the producer computes and actually exports tau=iota composed with sigma before the cut. The image of tau is iota applied to the actual image of sigma, so this normalization cannot increase its number of distinctions. If iota merges values, this is a changed encoder; the old sigma is not retained after entry. No separate advice, clock, phase, pointer, trace, decoder, variable address or source-dependent table remains accessible. NativeClassRootImage.imageOriginEquiv puts acquired full class values and actual origins in bijection, so exporting a function of ImageValues is exactly the normalized acquired-data contract, rather than an extra observation port.")),
            Paragraph(Text("A root table has precisely the same carriers and fixed outputs, but each running state queries one genuinely occurring class. Its four-reply next table keeps an arbitrary absent entry, although a class root is always reached. Every invocation costs one, including repeated or constant-on-chart questions. An empty class type forces the running carrier to be empty. The bounded evaluator returns the halt and the entire list of running-state visits; this mathematical list is used to specify paths and is not machine workspace. A running state after the final allowed call fails, while an initial or early halt succeeds.")),
            Describe.Lean(DescribeId.Create("nativesharedmoore-native-evaluate-iff"),
                DeclarationHandle.Create(Prefix + "native_evaluate_iff"), H("Native Execution and Exact Calls"),
                StatementSource.FromAuthor(Disp(EvaluatorStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For arbitrary running and halting types, every source, fuel q, initial state, halt and running-state list, evaluate(nativeStep,q,k) equals some(h,tr) exactly when the original native Run holds with that same tr and halt and length(tr) at most q. Each read constructor corresponds to one recursive call. The converse reconstructs the original Run without changing the controller model."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativesharedmoore-paid-native-recode"),
                DeclarationHandle.Create(Prefix + "paid_native_recode"), H("Paid Recoding on the Same Carriers"),
                StatementSource.FromAuthor(Disp(PaidStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For nonempty classes, installedWordBound is the maximum address length over every installed running state, including unused entries. padded_native_query_chart supplies one simultaneous truthful actual filling and origin for every attained type at this bound. Their types, full actual origin property, deep branch values and complete target equality are retained. The original firstClass, classReply and firstClass_reply classify each installed address. If no class is entered, the root table really queries a chosen existing class d0 and ignores the answer through a constant response map. If a hole is entered, its original shared class is queried: an empty suffix forwards the root reply; a proper suffix sends leaves to absent and padded branches to branch. The fourth unreachable reply can be arbitrary.")),
                    Paragraph(Text("paidTable preserves exactly Q, H and every halt output. Its next rule depends only on the installed running state and the one reply. The theorem gives equality of the complete evaluator result for every type, every fuel and every initial state on the selected actual origin. Thus all corresponding paths, invocation counts and halts agree, including early halts, convergences, repeated coordinates, unused states and cyclic union graphs. The new coloring is the original export evaluated on these selected actual fillings; its actual range is a subset of the original export range. No fixed arbitrary encoder is asserted constant on type fibers, and no execution-history unrolling is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativesharedmoore-install-full-fiber"),
                DeclarationHandle.Create(Prefix + "install_full_fiber"), H("Installation on Every Original Origin"),
                StatementSource.FromAuthor(Disp(InstallStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The producer inspects the roots of its actually acquired class terms and computes exportCode(c,v), the initial state c(theta(v)). This is a new complete code actually exported before the access cut under the supplied services. Every attained type has a truthful actual filling, so the actual export range equals the range of c. install replaces each coordinate by NativeWholeRowService.representative C d and keeps the carriers, four transitions and complete outputs. The first and third public conjuncts of native_full_root_feasibility give the complete target and exact representative readout. Consequently every actual origin, with arbitrary finite branch shapes, has the same complete evaluator path as its root input. Neither the padded necessity witnesses nor their depth bound restrict this direction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativesharedmoore-shared-moore-feasibility"),
                DeclarationHandle.Create(Prefix + "shared_moore_feasibility"), H("Identical Three Upper Budgets"),
                StatementSource.FromAuthor(Disp(TransferStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every nonempty full actual fiber, r at least one, K at least one and q at least zero, native and root joint feasibility are equivalent. The budgets count actual exported initial-state distinctions, all installed running plus halting states, and every invocation. Necessity uses the paid same-carrier recoding; sufficiency uses actual acquired-root export and representative addresses on the entire original fiber. With no reached classes, the chart has one empty function and the complete target is fixed. Necessity explicitly installs one halt, one code and no running state. No nonexistent coordinate and no dummy native call is introduced."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativesharedmoore-terminating-path-nodup"),
                DeclarationHandle.Create(Prefix + "terminating_path_nodup"), H("One Source Has No Repeated Running State"),
                StatementSource.FromAuthor(Disp(NoRepeatStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For any fixed deterministic step function, every successful bounded evaluator path has a duplicate-free running-state list. A suffix beginning at a repeated state would be the same terminating path by determinism but strictly shorter, contradicting equality of their lengths. This fixes one stationary input. It places no acyclicity condition on the union of paths for different inputs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativesharedmoore-arbitrary-carrier-completeness"),
                DeclarationHandle.Create(Prefix + "arbitrary_carrier_completeness"), H("All Finite Carriers and Unused Outputs"),
                StatementSource.FromAuthor(Disp(CarrierStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every correct finite root table on arbitrary carriers is represented by an accepted candidate on Fin(card Q) plus Fin(card H). The enumeration uses explicit finite lists and List.pi, including all coordinate maps, four reply transitions into the same state set, fixed attained-output maps and all initial colorings. Canonical split partitions cover every finite running/halting partition by separate carrier equivalences. These equivalences are used only in the proof; no noncomputable equivalence supplies executable search data. State counts, color-range cardinalities and complete paths are transported. An unused halt whose output is not attained is assigned one fixed attained output. The evaluator does not inspect halt outputs, and every actually reached halt already has its correct attained output, so no attained path or output changes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativesharedmoore-synthesize-sound"),
                DeclarationHandle.Create(Prefix + "synthesize_sound"), H("Returned Tables Solve the Full Fiber"),
                StatementSource.FromAuthor(Disp(SoundStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A returned candidate has an actually computed acquired-root initial code with actual range at most r, exactly its installed sum carrier with cardinality at most K, and a native Run terminating with the whole canonical predecessor row within q invocations on every original actual origin. Soundness applies the finite Boolean check, the exact native Run/evaluator equivalence and the full-fiber installation. The complete output includes the inverse exterior, restricted canonical class partition with every equality and disequality, and every predecessor absence guard."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativesharedmoore-finite-shared-synthesis"),
                DeclarationHandle.Create(Prefix + "finite_shared_synthesis"), H("Executable Arbitrary-Row Decision"),
                StatementSource.FromAuthor(Disp(SynthesisStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The finite procedure considers every positive total size through K and checks every attained chart input. A failed bounded run or an incorrect complete output rejects that input. It never tests whether the union graph is a DAG. Completeness combines same-carrier transfer, arbitrary-carrier reindexing, preservation under replacement of unused outputs and complete finite function enumeration. A positive result is a finite acquired encoder and one fixed-address native table for the original full fiber. No native address-length bound is an input. The construction decides existence in the explicit bounded-table model; it does not extract used states, longest words or a finite table from arbitrary program text."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativesharedmoore-check-spec"),
                DeclarationHandle.Create(Prefix + "check_spec"), H("Exact Finite Checker"),
                StatementSource.FromAuthor(Disp(CheckStatement())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The Boolean check is true exactly when the actual attained color range has at most r elements and every attained input reaches its correct complete target within q calls. This statement includes early halts, duplicate output values, arbitrary transition cycles and the failure of a still-running state at exhausted fuel."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativesharedmoore-complete-output-lower"),
                DeclarationHandle.Create(Prefix + "complete_output_lower"), H("Complete-Output Halt Bound"),
                StatementSource.FromAuthor(Disp(LowerStatement())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Let m be targetCount C, the number of distinct attained complete predecessor rows. A recovered actual valuation supplies an attained chart point, so m is positive on every nonempty original fiber. Every correct root table has at least m halts. The factorization and actual attained witnesses identify this same output set with the outputs on the original actual fiber, so the identical bound applies to a native solution. Equal-output and unused halts cannot reduce the count. This cardinal bound is also used to reject insufficient total-state budgets before finite search."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativesharedmoore-zero-call-endpoint"),
                DeclarationHandle.Create(Prefix + "zero_call_endpoint"), H("Exact Zero-Call Endpoint"),
                StatementSource.FromAuthor(Disp(ZeroStatement())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("At zero calls every initial state is already a halt. Distinct targets require distinct actual exported states and distinct fixed-output halts. Conversely the table consists of exactly one halt per attained complete row and exports that halt's code, computed from acquired roots. Thus feasibility is exactly r at least m and K at least m, on either side of the transfer. A constant target has the endpoint r=K=1,q=0. With no reached classes the exterior is the entire current tree, even for a nonempty blocked cut. An empty cut is of this form. A root cut has both beta and branch types but the same one-hole predecessor row. Cuts already blocked remain absent by NativeDepthPatterns.original_present_transport. Newly reached addresses extend an original beta leaf by one edge: the absent-address clause of actual_address_geometry, the same transport, and the two substituted leaf shapes give this exact parent. canonicalRow_absent_guard retains the concrete strict-prefix blocking leaf in the complete row. The public factorization in native_full_root_feasibility identifies its old mask with H(P,u) and its target with this entire predecessor row; right_birth also gives the right-sibling alpha criterion. Thus already blocked cuts and newly blocked beta-parent guards are both retained in every installed output. In particular r=1,q=0 is feasible exactly when m=1 and K is at least one."))), DescribeRole.Theorem),
            Paragraph(Text("The concrete checker input cyclicInput uses the one-hole current row, two running states a,b both querying its root class and one halt h carrying the complete one-hole predecessor row. Beta enters a and follows a,b,h; branch enters b and follows b,a,h. Both make two calls. The actual origins alpha and beta have current images beta and E=pair(beta,alpha), respectively, so both paths belong to the same original actual row fiber. The union contains a to b to a, while each fixed-source list is duplicate-free. Other replies halt. The finite checker accepts this input and its soundness gives a full-fiber solution through actual representative-root queries and acquired code export. Finite synthesis may return the cheaper constant halt for the same row; selecting this cyclic table is not a requirement.")),
            Paragraph(Text("Classical state-associated output terminology is attributed to Edward F. Moore, Gedanken-Experiments on Sequential Machines, Automata Studies, DOI 10.1515/9781400882618-006. This attribution imports no external minimization theorem and makes no claim to verification of the full paper. The actual image grammar, unique inverse, complete row fiber and simultaneous finite padding are the existing NativeClassRootImage, NativeCutFibers, NativeFullRootFeasibility and NativeClassRootPadding results. Finite enumeration and deterministic induction are ordinary methods; no global novelty claim is made.")),
            Paragraph(Text("Acquisition, genuine actual export, complete access isolation, authenticated one-update continuity, lawful common entry and stationary native service are supplied paid premises. The mathematical export construction does not establish those physical services. Same-r,K,q feasibility preserves neither an arbitrary fixed encoder pointwise, every original native trace on every source, address width, installed tables or whole-output storage, total physical memory, acquisition/export work, entry implementation nor service time. The exact necessity comparison is with one selected actual origin per type; the newly installed sufficient table is correct on every actual origin. A charged constant recoding is a real class query, not a free phase. Zero fresh calls do not mean zero acquisition. Computed addresses or unbounded workspace require a separate proof that the total configurations satisfy the finite stationary table contract."))
        )));
    private static Formula EvaluatorStatement()
    {
        return Carriers(All("M",Call("Controller",V("Q"),V("H")),All("t",V("Source"),
            All("n",V("Nat"),All("k",Sum(),All("h",V("H"),All("tr",Call("List",V("Q")),
            Iff(EqOf(Call("evaluate",Call("nativeStep",V("M"),V("t")),V("n"),V("k")),
                Call("some",Pair(V("h"),V("tr")))),
                And(Call("Run",V("M"),V("t"),V("k"),V("tr"),V("h")),
                    LeOf(Call("length",V("tr")),V("n")))))))))));
    }
    private static Formula PaidStatement()
    {
        var c=Current(); var theta=V("theta"); var values=App(V("values"),theta);
        var origin=Call("value",App(V("origins"),theta));
        var truth=All("theta",Call("Chart",c),And(
            EqOf(Call("rho",origin),Call("fill",c,values)),
            EqOf(Call("types",c,values),Call("value",theta)),
            Call("DeepValues",c,Call("installedWordBound",V("M")),values),
            EqOf(Call("target",c,Call("value",theta)),Call("canonicalRow",V("P"),origin))));
        var paths=All("theta",Call("Chart",c),All("n",V("Nat"),All("k",Sum(),
            EqOf(Call("evaluate",Call("rootStep",Call("paidTable",c,V("d"),V("M")),Call("value",theta)),V("n"),V("k")),
                Call("evaluate",Call("nativeStep",V("M"),Call("rho",origin)),V("n"),V("k"))))));
        return Carriers(Finite("Q",All("P",V("CutSet"),Imp(Call("CutPrefixFree",V("P")),
            All("uo",V("Source"),All("d",Call("Classes",c),All("M",Call("Controller",V("Q"),V("H")),
            Some("values",Fn(Call("Chart",c),Call("ImageValues",c)),
            Some("origins",Fn(Call("Chart",c),Call("OriginFiber",V("P"),c)),And(truth,paths))))))))));
    }
    private static Formula InstallStatement()
    {
        var c=Current(); var v=V("v"); var u=V("u");
        var types=Call("types",c,v); var export=Call("exportCode",V("hP"),V("uo"),V("color"));
        var result=And(EqOf(Call("range",export),Call("range",V("color"))),
            All("v",Call("ImageValues",c),All("u",Call("OriginFiber",V("P"),c),
            Imp(EqOf(Call("rho",Call("value",u)),Call("fill",c,v)),And(
                EqOf(Call("target",c,types),Call("canonicalRow",V("P"),Call("value",u))),
                All("n",V("Nat"),All("k",Sum(),EqOf(
                    Call("evaluate",Call("nativeStep",Call("install",V("T")),Call("rho",Call("value",u))),V("n"),V("k")),
                    Call("evaluate",Call("rootStep",V("T"),types),V("n"),V("k"))))))))));
        return Carriers(All("P",V("CutSet"),All("hP",Call("CutPrefixFree",V("P")),
            All("uo",V("Source"),All("T",Call("RootTable",c,V("Q"),V("H")),
            All("color",Fn(Call("Chart",c),Sum()),result))))));
    }
    private static Formula TransferStatement()
    {
        return FiberBudgets(Imp(And(LeOf(D(1),V("r")),LeOf(D(1),V("K"))),
            Iff(Call("NativeFeasible",V("P"),Current(),V("r"),V("K"),V("q")),
                Call("RootFeasible",Current(),V("r"),V("K"),V("q")))));
    }
    private static Formula NoRepeatStatement()
    {
        return Carriers(All("step",Fn(V("Q"),Sum()),All("n",V("Nat"),All("k",Sum(),
            All("h",V("H"),All("tr",Call("List",V("Q")),Imp(
                EqOf(Call("evaluate",V("step"),V("n"),V("k")),Call("some",Pair(V("h"),V("tr")))),
                Call("Nodup",V("tr")))))))));
    }
    private static Formula CarrierStatement()
    {
        var ca=Call("card",V("Q")); var cb=Call("card",V("H"));
        var exists=Some("A",Call("Candidate",V("C"),ca,cb),And(
            Seq(V("A"),Sp,InMacro,Sp,Call("candidates",V("C"),ca,cb)),
            EqOf(Call("check",V("A"),V("r"),V("q")),V("true"))));
        return All("C",V("LiteralRow"),Imp(Call("Nonempty",Call("Chart",V("C"))),Carriers(
            Finite("Q",Finite("H",All("T",Call("RootTable",V("C"),V("Q"),V("H")),
            All("color",Fn(Call("Chart",V("C")),Sum()),All("r",V("Nat"),All("q",V("Nat"),
            Imp(And(LeOf(Call("ncard",Call("range",V("color"))),V("r")),Correct(V("C"))),exists))))))))));
    }
    private static Formula CheckStatement()
    {
        return All("C",V("LiteralRow"),All("a",V("Nat"),All("b",V("Nat"),
            All("A",Call("Candidate",V("C"),V("a"),V("b")),All("r",V("Nat"),All("q",V("Nat"),
            Iff(EqOf(Call("check",V("A"),V("r"),V("q")),V("true")),
                Call("Checked",V("A"),V("r"),V("q")))))))));
    }
    private static Formula LowerStatement()
    {
        return All("C",V("LiteralRow"),Carriers(Finite("H",
            All("T",Call("RootTable",V("C"),V("Q"),V("H")),
            All("color",Fn(Call("Chart",V("C")),Sum()),All("q",V("Nat"),
                Imp(Correct(V("C")),LeOf(Call("targetCount",V("C")),Call("card",V("H"))))))))));
    }
    private static Formula ZeroStatement() => All("C",V("LiteralRow"),All("r",V("Nat"),All("K",V("Nat"),
        Iff(Call("RootFeasible",V("C"),V("r"),V("K"),D(0)),And(
            LeOf(Call("targetCount",V("C")),V("r")),LeOf(Call("targetCount",V("C")),V("K")))))));
    private static Formula SynthesisStatement() => FiberBudgets(
        Imp(And(LeOf(D(1),V("r")),LeOf(D(1),V("K"))),Iff(
            EqOf(Call("isSome",Call("synthesize",Current(),V("r"),V("K"),V("q"))),V("true")),
            Call("NativeFeasible",V("P"),Current(),V("r"),V("K"),V("q")))));
    private static Formula SoundStatement()
    {
        var c=Current(); var a=V("A"); var table=Call("table",a); var color=Call("color",a);
        var export=Call("exportCode",V("hP"),V("uo"),color); var v=V("v"); var u=V("u");
        var actual=All("v",Call("ImageValues",c),All("u",Call("OriginFiber",V("P"),c),
            Imp(EqOf(Call("rho",Call("value",u)),Call("fill",c,v)),
                Some("h",Call("Halts",a),Some("tr",Call("List",Call("Running",a)),And(
                    Call("Run",Call("install",table),Call("rho",Call("value",u)),App(export,v),V("tr"),V("h")),
                    EqOf(Call("out",table,V("h")),Call("canonicalRow",V("P"),Call("value",u))),
                    LeOf(Call("length",V("tr")),V("q"))))))));
        var result=And(LeOf(Call("ncard",Call("range",export)),V("r")),
            LeOf(Call("card",Call("States",a)),V("K")),actual);
        return All("P",V("CutSet"),All("hP",Call("CutPrefixFree",V("P")),All("uo",V("Source"),
            Budgets(All("A",Call("BoundedCandidateType",c),Imp(
                EqOf(Call("synthesize",c,V("r"),V("K"),V("q")),Call("some",a)),result))))));
    }
    private static Formula Correct(Formula c) => All("theta",Call("Chart",c),Some("h",V("H"),
        Some("tr",Call("List",V("Q")),And(
            EqOf(Call("evaluate",Call("rootStep",V("T"),Call("value",V("theta"))),V("q"),App(V("color"),V("theta"))),
                Call("some",Pair(V("h"),V("tr")))),
            EqOf(Call("out",V("T"),V("h")),Call("target",c,Call("value",V("theta"))))))));
    private static Formula Current() => Call("canonicalRow",V("P"),Call("rho",V("uo")));
    private static Formula Sum() => Call("Sum",V("Q"),V("H"));
    private static Formula Carriers(Formula b) => All("Q",V("Type"),All("H",V("Type"),b));
    private static Formula Finite(string n, Formula b) => Seq(OpenBracket,Call("Fintype",V(n)),CloseBracket,Comma,Sp,b);
    private static Formula Budgets(Formula b) => All("r",V("Nat"),All("K",V("Nat"),All("q",V("Nat"),b)));
    private static Formula FiberBudgets(Formula b) => All("P",V("CutSet"),Imp(Call("CutPrefixFree",V("P")),
        All("uo",V("Source"),Budgets(b))));
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Pair(Formula a, Formula b) => Seq(Open,a,Comma,Sp,b,Close);
    private static Formula App(Formula f, Formula a) => new Formula.Apply(f,[a]);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))), [..a]);
    private static Formula Fn(Formula a,Formula b) => Seq(Par(a),Sp,To,Sp,Par(b));
    private static Formula EqOf(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a,Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f,i)=>i==0?Par(f):Seq(Sp,Land,Sp,Par(f))).ToArray());
    private static Formula Imp(Formula a,Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b) => Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Iff(Formula a, Formula b) => Seq(a, Sp, Leftrightarrow, Sp, b);
}
