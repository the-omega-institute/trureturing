using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeIndependentExecutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeIndependentExecution.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeIndependentExecution", H("Independent writer execution and native constraints"), Blocks(
            Def("Op", "Source-blind observer microsteps", "The transition delta receives only the accessible configuration C. It produces one local successor, one fully materialized literal address with four continuations, or Return. A local calculation can take arbitrarily many such steps. Return hands off the whole current configuration, including all accessible control and storage distinctions represented by C."),
            Def("ObserverEvent", "All observer events", "The finite event word retains every local microstep, each literal address and supplied four-valued reply, and a separate Return."),
            Def("Event", "Independent updates and observer events", "An active event is one writer substitution or one observer event. Idle waiting and unobservable writer bookkeeping are outside this word."),
            Def("Word", "Finite active raw words", "A Word is the chronological list of all active events, with no quotient by update placement."),
            Def("TimedWord", "Burst annotated skeletons", "Each observer event carries the finite number of writer substitutions immediately preceding it. These counts are unbounded natural numbers and are mathematical annotations, never observer inputs."),
            Def("expand", "Insertion of independent writer bursts", "expand inserts each finite burst before its observer event. It includes updates before the first event, every local step, every Read and the separate Return."),
            Def("Skeleton", "Actual program transitions with hypothetical replies", "A skeleton starts at the supplied accessible configuration and follows delta one microstep at a time. Reads may receive any of the four replies. The final event is Return with exactly b as the entire accessible configuration. Burst annotations do not influence the source-blind program transitions."),
            Def("Run", "Separately defined actual execution", "Run carries one actual source register. An independent update applies native substitution without inspecting or changing observer control. A local step changes control only. A Read requires the actual readout at its literal address and follows the corresponding continuation. Return ends the active word and delivers the current whole configuration."),
            Def("constraint", "One finite formula for an erased skeleton", "constraint i traverses only the observer event list, using original coordinate i at that event and incrementing the coordinate after every event. Each Read contributes its finite native navigation formula; the remaining events contribute no tree condition. All occurrences preserve one original source. The formula is independent of the supplied epoch values and burst counts."),
            Def("Chronology", "Exact mathematical event counts", "Chronology e i t eta states that each event coordinate equals the preceding epoch plus that event's finite burst. It retains counts at local steps and Return, even though those events add no tree equation."),
            Def("Ordered", "Finite nondecreasing epoch vectors", "Ordered e i events eta requires the first supplied epoch to be at least e and each later epoch to be at least its predecessor. It constrains only the finite event list and has no common bound."),
            Def("retime", "Chronological difference insertion", "retime replaces burst annotations by consecutive differences of the supplied event epochs. Its initial difference uses e. Nondecreasing epochs make each difference exact in the natural numbers."),
            Def("erase", "Recovery of every update placement", "erase removes writer events and counts each maximal update burst immediately preceding the next observer event. A legal returning word has no unassigned trailing update burst."),
            Theorem("updates_iff", "Exact insertion of a finite independent burst", Updates(),
                "A burst of k genuine writer substitutions before the supplied suffix is equivalent to starting that same suffix at the kth iterate. All observer configurations, the complete suffix word and the whole returned configuration are preserved. The burst count is a mathematical annotation, not an observer input."),
            Theorem("chronological_execution", "Native constraints realize every chronological schedule", Chronological(),
                "Every finite source-blind skeleton and every supplied nondecreasing epoch vector satisfy this equivalence. Native formula satisfaction constructs an actual independent-writer execution by successive difference insertion. Conversely, the actual execution supplies every literal Read equation. Induction preserves the same original u, all adaptive local states, each materialized address and the exact whole terminal b. No liveness premise is used."),
            Theorem("native_history_correspondence", "Exact active histories and all projections", History(),
                "Erasure after insertion recovers every burst annotated word. Every legal finite returning execution is exactly the expansion of a skeleton satisfying its native formula at chronological counts, and conversely. Equality retains placement relative to all local steps and Return. The final clause gives every projection pi of this recovered word: a constant projection gives the source fiber; selecting cumulative event counts at fixed or finitely specified roles gives the source and designated epoch relation. Different possible schedules are not assertions about the authenticated actual past."),
            Def("Instruction", "Finitely encoded microstep instructions", "An instruction is a local successor control, a literal address with four successor controls, or Return. Every natural control encodes an entire accessible finite configuration, without a uniform size bound."),
            Def("continuation", "Four acquired-reply successors", "The four finite controls are selected in the order alpha, beta, branch and absent. This selection uses only the actual acquired reply."),
            Def("instruction", "Operational meaning of finite instructions", "Read instructions materialize their literal address and all four control successors; local instructions change control; Return preserves the whole terminal control."),
            Def("EffectiveProgram", "Finite recursive code for each microstep", "A program supplies finite partial-recursive code, its total instruction function and an all-control realization equation. One evaluation computes one observer microstep. Divergent sequences of local steps are not replaced by a total next-external-action oracle."),
            Def("evalInstruction", "Bounded recursive-code decoding", "A finite code evaluation either supplies a decoded finite instruction or yields no result at the supplied fuel. Increasing fuel eventually supplies the realized instruction at every individual control."),
            Def("replies", "The complete reply alphabet", "The finite list contains alpha, beta, branch and absent, each once."),
            Def("enumerate", "Finite exploration with two bounds", "The evaluator fuel bounds the recursive-code evaluation at each microstep, while depth bounds the number of observer events explored. Every Read explores all four continuations. Return emits the exact whole control. Every invocation is finite, including those exploring a branch that has infinitely many local steps."),
            Def("untimed", "Zero-burst representation of an erased word", "untimed marks each observer event with a zero burst. These markers describe the source-blind skeleton; retime supplies the actual chronological writer bursts."),
            Theorem("effective_native_correspondence", "Code exploration and exact native execution", Effective(),
                "The union over evaluator fuel and microstep depth contains exactly the source-blind returning skeletons. Every one has the native constraint semantics at every chronological epoch vector. Soundness follows each decoded instruction; completeness bounds the finitely many code computations on a returning skeleton. Finite depth prevents a divergent hypothetical branch from blocking exploration of another branch. The entire terminal control b is preserved."),
            Paragraph(Text("In these formulas map snd t is t.map Prod.snd, iterate is Function.iterate, and Holds is Formula.Holds with its formula argument last. The variable eta assigns natural exponents to event coordinates. Pi may retain any mathematical projection of the recovered burst annotated word.")),
            Paragraph(Text("The operational results quantify arbitrary control types and source-blind transition functions. The code-based extension gives an executable, sound and complete bounded exploration on naturally encoded controls. Formal partial-recursive encoding theorems for this exploration and the native formula generator are separate statements and are not asserted here. A different finite-string configuration representation requires its instruction realization equation; mere encodability does not supply it.")),
            Paragraph(Text("No supplemental row or comparison assertion is attached to these constraints. Such assertions require separate soundness proofs about actual acquisition events. Formula satisfaction cannot make an incorrect producer's retained assertions true."))
        )));
    private static DocumentBlock Def(string n,string title,string prose) => Describe.Lean(
        DescribeId.Create("native-independent-"+(n == "Instruction" ? "instruction-data" : n.Replace('.', '-').ToLowerInvariant())),DeclarationHandle.Create(Prefix+n),
        H(title),StatementSource.WithoutFormula(),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),DescribeRole.Definition);
    private static DocumentBlock Theorem(string n,string title,Formula formula,string prose) => Describe.Lean(
        DescribeId.Create("native-independent-"+n.Replace('_','-')),DeclarationHandle.Create(Prefix+n),H(title),
        StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),DescribeRole.Theorem);
    private static Formula Updates()
    {
        Formula f=IffOf(Run(V("U"),Call("append",Call("replicate",V("k"),Call("update")),V("t"))),
            Run(Call("iterate",V("substitution"),V("k"),V("U")),V("t")));
        return All("C",V("Type"),All("delta",Arr(V("C"),Call("Op",V("C"))),
            All("k",V("Nat"),All("c",V("C"),All("U",V("Source"),
                All("t",V("Word"),All("b",V("C"),f)))))));
    }
    private static Formula Chronological()
    {
        Formula f = IffOf(Holds("i","t"),Run(Call("iterate",V("substitution"),V("e"),V("u")),
            Call("expand",Call("retime",V("e"),V("i"),Events("t"),V("eta")))));
        f=Imp(Call("Ordered",V("e"),V("i"),Events("t"),V("eta")),f);
        f=All("x",Arr(V("Nat"),V("Source")),f);
        f=All("eta",Arr(V("Nat"),V("Nat")),f);
        f=All("i",V("Nat"),f); f=All("e",V("Nat"),f); f=All("u",V("Source"),f);
        f=Imp(Skel("t"),f); f=All("t",V("TimedWord"),f);
        return Program(f);
    }
    private static Formula Effective()
    {
        Formula delta = Call("transition",V("P"));
        Formula execution = Call("Run",delta,V("c"),V("u"),
            Call("expand",Call("retime",D(0),D(0),V("w"),V("eta"))),V("b"));
        Formula semantics = Imp(Call("Ordered",D(0),D(0),V("w"),V("eta")),
            IffOf(Call("Holds",V("u"),V("eta"),V("x"),Call("constraint",D(0),V("w"))),execution));
        semantics = All("u",V("Source"),All("eta",Arr(V("Nat"),V("Nat")),
            All("x",Arr(V("Nat"),V("Source")),semantics)));
        Formula listed = Exists("fuel",V("Nat"),Exists("n",V("Nat"),
            Seq(Seq(Open,V("w"),Comma,Sp,V("b"),Close),Sp,InMacro,Sp,
                Call("enumerate",Call("code",V("P")),V("fuel"),V("n"),V("c")))));
        Formula f = IffOf(listed,And(Call("Skeleton",delta,V("c"),Call("untimed",V("w")),V("b")),semantics));
        return All("P",V("EffectiveProgram"),All("c",V("Nat"),All("b",V("Nat"),
            All("w",Call("List",V("ObserverEvent")),f))));
    }
    private static Formula History()
    {
        Formula inverse = All("t", V("TimedWord"),
            EqOf(Call("erase", Call("expand", V("t"))), V("t")));
        Formula rhs = And(Skel("t"), Chron(), HoldsZero(),
            EqOf(Call("expand", V("t")), V("h")),
            EqOf(Call("erase", V("h")), V("t")));
        rhs = Exists("t", V("TimedWord"),
            Exists("eta", Arr(V("Nat"), V("Nat")), rhs));
        Formula raw = All("h", V("Word"), IffOf(Run(V("u"), V("h")), rhs));
        Formula lhsProjection = Exists("h", V("Word"),
            And(Run(V("u"), V("h")), EqOf(Call("pi", Call("erase", V("h"))), V("d"))));
        Formula rhsProjection = And(Skel("t"), Chron(), HoldsZero(), EqOf(Call("pi", V("t")), V("d")));
        rhsProjection = Exists("t", V("TimedWord"),
            Exists("eta", Arr(V("Nat"), V("Nat")), rhsProjection));
        Formula projected = IffOf(lhsProjection, rhsProjection);
        projected = All("d", V("D"), projected);
        projected = All("pi", Arr(V("TimedWord"), V("D")), projected);
        projected = All("D", V("Type"), projected);
        Formula f = And(inverse, raw, projected);
        f = All("x", Arr(V("Nat"), V("Source")), f);
        return Program(All("u", V("Source"), f));
    }
    private static Formula Program(Formula f)
    {
        f = All("b", V("C"), f);
        f = All("c", V("C"), f);
        f = All("delta", Arr(V("C"), Call("Op", V("C"))), f);
        return All("C", V("Type"), f);
    }
    private static Formula Events(string t) => Call("map",V("snd"),V(t));
    private static Formula Skel(string t) => Call("Skeleton",V("delta"),V("c"),V(t),V("b"));
    private static Formula Chron() => Call("Chronology",D(0),D(0),V("t"),V("eta"));
    private static Formula HoldsZero() => Call("Holds",V("u"),V("eta"),V("x"),Call("constraint",D(0),Events("t")));
    private static Formula Holds(string i,string t) => Call("Holds",V("u"),V("eta"),V("x"),Call("constraint",V(i),Events(t)));
    private static Formula Run(Formula u,Formula t) => Call("Run",V("delta"),V("c"),u,t,V("b"));
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] xs) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[.. xs]);
    private static Formula Arr(Formula a,Formula b) => Seq(a,Sp,To,Sp,b);
    private static Formula EqOf(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula IffOf(Formula a,Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Imp(Formula a,Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f,i)=>i==0?Par(f):Seq(Sp,Land,Sp,Par(f))).ToArray());
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Exists(string n,Formula t,Formula b) => Seq(F.Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
