using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeSourceSelectorCodeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed executable numeric selector with exact raw-instruction and original-state realization laws.",
        H("Executable Numeric Selector"), Blocks(
            Entry("tickCode", "Raw workspace instructions", "The program uses the pinned Nat.Partrec.Code constructors. Products use Nat.pair, a list cell uses one plus the paired head and tail, and sums use doubled payloads with parity tags. Zero tests first use pairing and unpairing to make a zero-or-one counter; primitive recursion for this test then has at most one recursive step. Numeric scans test every Boolean in an address and every address-valued frame in the stack. The program replaces a failed control test by zero, the encoding of numericInitial. Its visit branch constructs the complete read address and four continuations, including the absent continuation. Its deliver branch distinguishes an empty stack, a pending address and a saved numeric name. These operations use numeric data throughout; they do not decode Source values.", DescribeRole.Definition),
            Entry("workspaceCode", "Numeric first return", "A primitive-recursion program iterates the encoded numeric step. Minimization searches for the first instruction with the action tag, and the program returns that instruction's full action payload. Its equality with PFun.fix of numericTick follows from the universal raw-instruction realization and the conditional first-return theorem. No finite bound on workspace, stack, address or search index is introduced.", DescribeRole.Definition),
            Entry("selectorCode", "Closed original-state program", "The input projection extracts the workspace from the nested product encoding of OriginalState. The program then applies workspaceCode. Common input, epoch and retained history remain outside this selector computation, as in sourceService. The program data contains constructors, composition, recursion, minimization and computable constants. It contains no classical choice or semantic sourceDecoder.", DescribeRole.Definition),
            Entry("evaluate", "Existing bounded evaluation", "The program is supplied directly to evalOriginalActionFromCode, which evaluates with magnitude and recursion fuel 2 raised to the supplied stage and decodes the full OriginalAction Nat. A missing bounded value is not evidence of divergence.", DescribeRole.Definition),
            Entry("controller", "Existing controller", "originalNativeControlFromCode consumes exactly the same selectorCode. The original controller retains its state decoding, four reply continuations and acquired-history transitions. Its local events are evaluator work and do not identify the producer's local chronology.", DescribeRole.Definition),
            Entry("tick_code_correct", "Universal raw instruction", "For every natural workspace, tickCode evaluates to the complete encoded numericTick instruction. The finite scan invariant covers every raw list cell. Boolean-address checks and all address-valued frames exactly match recursive decoder definedness, and any successfully decoded NumericControl re-encodes to the original natural number. A failed decode therefore uses exactly numericInitial. Two reversals compute each appended child address. Visit constructs all four reply continuations; deliver handles an empty stack, a pending address and a saved name. The proof also accounts for the primitive-recursion branch evaluating its zero case before a positive case.", DescribeRole.Theorem),
            Entry("workspace_code_correct_of_tick", "Exact conditional first return", "Assume that tickCode evaluates to the complete encoded numericTick instruction on every natural workspace. Then workspaceCode agrees with selectWorkspace, after encoding the returned action, on every natural workspace. This is equality of partial values, so it includes definedness. The proof computes quotient and parity exactly, identifies the minimization index with the first action, and directly uses Partrec.fix_aux to connect the numeric iterates to the existing first-return function. It introduces no state restriction, finite fuel premise or new source traversal.", DescribeRole.Theorem),
            Entry("realizationOfTick", "Conditional original-state realization", "Given the same universal instruction premise, extract the workspace from the genuine OriginalState encoding and use the first-return law to build the existing OriginalCodeRealization sourceService with code exactly selectorCode. The universal tick_code_correct theorem supplies this premise; realization applies the builder to it. The existing original_code_service_simulation applies to the resulting record whenever the premise is supplied.", DescribeRole.Definition),
            Entry("selector_code_correct", "Exact original-state equality", "On every genuine OriginalState, evaluating selectorCode on its encoded state equals sourceService.select with its complete returned action encoded. Equality of partial values preserves both values and definedness, including divergence. The proof supplies tick_code_correct to realizationOfTick, which uses workspace_code_correct_of_tick and the existing first-return bridge. Common input, epoch, history, arbitrary numeric workspace, invalid encodings and all reply continuations retain their original domains.", DescribeRole.Theorem),
            Entry("realization", "Existing realization consumer", "The record has code exactly selectorCode and realizes field selector_code_correct. It is directly admissible as the argument of the existing original_code_service_simulation. That theorem retains external reads and terminal observations after erasing evaluator steps; it does not identify evaluator microsteps with the producer chronology. No new traversal, controller or simulation is introduced.", DescribeRole.Definition),
            Paragraph(Text("The code data is computable and closed. The equations are unbounded semantic statements and supply no uniform running-time, memory or fuel bound. A bounded evaluation returning no value proves no divergence. No physical installation or Source-valued computational decoder follows."))
        )));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("native-source-code-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title),
            role == DescribeRole.Theorem ? StatementSource.FromAuthor(Disp(TheoremFormula(n)))
                : StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula TheoremFormula(string n) => n switch
    {
        "tick_code_correct" => All("n", V("Nat"), EqOf(Call("eval", V("tickCode"), V("n")),
            Call("some", Call("encode", Call("numericTick", V("n")))))),
        "selector_code_correct" => All("s", V("OriginalState"),
            EqOf(Call("eval", V("selectorCode"), Call("encode", V("s"))),
                Call("map", V("encode"), Call("select", V("sourceService"), V("s"))))),
        "workspace_code_correct_of_tick" => Imp(
            All("m", V("Nat"), EqOf(Call("eval", V("tickCode"), V("m")),
                Call("some", Call("encode", Call("numericTick", V("m")))))),
            All("n", V("Nat"), EqOf(Call("eval", V("workspaceCode"), V("n")),
                Call("map", V("encode"), Call("selectWorkspace", V("n")))))),
        _ => throw new System.ArgumentException("Unknown theorem", nameof(n))
    };
    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Close, Sp, Implies, Sp, Open, b, Close);
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Open, b, Close);

}
