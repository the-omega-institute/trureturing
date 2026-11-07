using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class FiniteAdaptiveSemanticFrontierReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/FiniteAdaptiveSemanticFrontierReplay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Semantic frontiers at different actual depths",
        H("Semantic frontiers at different actual depths"),
        Blocks(
            Paragraph(Text("The frontier is queried at every positive fuel. Each cut retains the original remaining fuel, node index, entire cache and partial assignment. Every marked valid context must have a proved semantic bound or raw replay acceptance for that same context; cache validity is passed to the receipt before frontier acceptance. Native counts and shared shapes supply neither receipt nor coverage.")),
            Node("check", "check", "Check an early frontier or continue the actual replay",
                "Fuel zero rejects. At positive fuel an accepted frontier terminates this branch. Otherwise the original bound and symmetry tests remain, and an actual split requires positive child fuel and acceptance of every finite value branch with its own updated cache and partial assignment.", DescribeRole.Definition),
            Node("checked-split", "checked_split", "Assemble every original child context",
                "An unmarked parent, its exact literal split-node equality, positive child fuel and acceptance of every actual finite-value child imply adaptive acceptance of the parent. Each child uses its actual remaining fuel, index, updated cache and partial assignment. The original EJM application must preserve all four outcomes and the actual base-four prefix updates.", DescribeRole.Theorem),
            Node("checked-forces-smaller-bad-event", "checked_forces_smaller_bad_event", "Every accepted context responds to a bad event",
                "Assume adaptive acceptance and validity of the exact current fuel, cache and partial assignment, a compatible event below the gap, sound lower bounds, valid split updates, score preservation and strict rank decrease for accepted symmetry cuts. The proved current cache invariant is passed to the frontier receipt. A semantic frontier bound contradicts a compatible bad completion. A raw frontier reuses the existing cached replay response, which supplies a strictly smaller-rank bad event. Unmarked bounds use proved cache validity; splits follow the compatible event through an actual branch; symmetry cuts preserve score and strictly decrease rank. A semantic receipt is never converted into raw check acceptance.", DescribeRole.Theorem),
            Node("checked-global-lower-bound", "checked_global_lower_bound", "Restart rank descent at the empty root",
                "Complete adaptive root acceptance, exact receipts for every marked valid context and the original invariant obligations imply the global gap by strong induction on event rank. A transformed bad event restarts at the empty root and need not satisfy its former partial assignment. Complete coverage and every receipt remain explicit premises.", DescribeRole.Theorem),
            Paragraph(Text("The original EJM bridge retains twenty coordinates, four values, F1/F2, all thirty-two blocks, scale 6987435, the original root and initial cache. Its global conclusion remains conditional on complete adaptive root acceptance, initial validity and semantic or exact raw receipts at every marked valid context. Cut counts, depth histograms and native success flags supply none of these premises. First-freeze checker admission requires an actually accepted complete input and its live soundness application with all concrete premises kernel checked; no complete EJM certificate acceptance is asserted here. Source-owned Reg evidence and current bindings for the three public theorems remain unfinished under https://github.com/the-omega-institute/trureturing/issues/16309.")))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
