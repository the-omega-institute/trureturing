using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class ActualCompletionPhaseReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionPhaseReplay.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original controller phases are replayed from coarse histories, resetting only the local history at phase boundaries.",
        H("Original Completion Phase Replay"),
        Blocks(
            Paragraph(Text("The phase observation contains the current route history, or the selected verifier, remaining literal leaf requests and verifier history, or the acquisition history. It discards previous phases' histories. The chronological first-occurrence raw cache remains the compiler's separate persistent decoder.")),
            Def("PhaseLabel", "Original phase observation", "Route, verifier and acquisition observations retain their respective local coarse histories; malformed histories have one fixed default observation."),
            Def("verifyPhase", "Original verifier replay", "Replay verifyController on quotient representatives. A successful leaf comparison advances the residual leaf list, and the first mismatch starts acquisition on the fresh unconsumed suffix."),
            Def("routePhase", "Original route replay", "Replay compileRaw on the coarse route. At its exit, the selected verifier or acquisition begins with an empty local history."),
            Def("phaseAlphabet", "Finite actual phase alphabet", "The image of all bounded-source terminal coarse prefixes under the original phase parser."),
            Def("observerPhase", "Installed phase observation", "Every retained compiler row carries its parsed original phase; the absorbing sink carries the fixed malformed label."),
            Describe.Lean(DescribeId.Create("actual-completion-phase-replay-contract"),
                DeclarationHandle.Create(Prefix + "phase_replay_contract"), H("Original action and phase replay"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive source budget and an original Strategy with the exact compileRaw/controllerPolicy policy equation, the parser computes the original action on every coarse history. It preserves the original route exit and verifier-failure resets. A route label is exactly the route-local consumed history. A verifier label identifies the same selected prototype, decomposes the initial requests into consumed addresses and the residual list, and retains exactly the consumed matching reports in its local history; a nonempty residual has exhausted the available input. Every actual compiled prefix carries its original local phase observation in the finite phase alphabet, and its parsed action equals the original strategy action. The statement does not replace phase labels with the full global history."))), DescribeRole.Theorem),
            Paragraph(Text("The finite prescribed-prefix checker, explicit route/verifier/acquisition horizon, and the marked and unmarked minimum-price formulas are separate obligations."))
        )));
    private static DocumentBlock Def(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-completion-phase-replay-" + n.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
