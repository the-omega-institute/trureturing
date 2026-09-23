using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class SharpChallengeInstrumentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite homogeneous challenge instrument separates fixed action words from causal feedback.",
        H("Sharp challenge instrument"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sharp-challenge"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SharpChallengeInstrument.result"),
                H("Exact fixed-word and feedback distances"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every number of actions m at least two and every horizon H at least two, write H = n + 2. Actions are Fin m. Hidden states are Start z, Awaiting z k r with k in Fin (n + 1), Fail, and Done. Observable symbols are Challenge r, Bit z, Failure, and Finished. The constructors distinguish all four kinds of output.")),
                    Paragraph(Text("The transition row is a probability mass function on an output and a successor state jointly. Start ignores the first action and draws a uniform challenge. A matching action at a positive countdown draws one new uniform challenge and decreases the countdown; that same draw is both emitted and stored. A match at countdown zero emits the hidden bit and enters Done. A mismatch emits Failure and enters Fail. Every action remains legal: Fail emits Failure forever, and Done emits Finished forever. There is no external time argument in the instrument.")),
                    Paragraph(Text("The initial accessible archive is the unique element of Unit. The two priors put unit mass on Start false and Start true. A length-t record is the entire chronological sequence of t action/output pairs, represented recursively as the previous record and the last pair. Execution samples the common history action distribution and then the instrument's joint row, appending both the action and the output. The policy receives only this accessible record. It receives neither the hidden state nor a future challenge.")),
                    Paragraph(Text("The policy class contains every stochastic probability row at every finite history, including unreachable histories. Sequential multiplication uses the same action factor and the same joint transition factor when earlier hidden states are fixed. A fixed action word is extended arbitrarily after H; those later actions do not affect the H-step law. Forgetting its deterministic actions gives the full output-word experiment.")),
                    Paragraph(Text("For each fixed word a, let alpha = (1/m) raised to the power (H - 1). The successful record consists of the prescribed actions, challenges a at positions two through H, and the final symbol Bit z. Its mass is alpha. The common failure function retains each earlier challenge/action prefix and every subsequent Failure symbol. At the first mismatch after k challenges the specified prefix has mass (1/m) raised to k; later absorbing outputs preserve that mass. The operational prefix induction gives the complete record law as this common failure function plus alpha at the successful record. The common part has total mass one minus alpha.")),
                    Paragraph(Text("The two successful records differ in the last bit symbol. Cancellation of the common failure part gives total variation alpha on full records and on full output words, for every fixed word. Consequently the maximum fixed-word distance is alpha.")),
                    Paragraph(Text("One common total matching policy chooses a fixed default first action and subsequently copies the last observed challenge, using the default after any other symbol. Its pending challenge always equals that last visible challenge. Under either initial bit it reaches Done at step H and emits Bit z, so the final-bit event separates the two complete record laws with total variation one. Every stochastic policy induces normalized finite record laws, whose total variation is at most one. Thus the supremum over the entire common stochastic policy class equals one and is attained by the matching policy.")),
                    Paragraph(Text("At H = 2 the first challenge is followed immediately by the single match test; for m = 2 each fixed word succeeds with mass one half. The state space changes with H. These are exact distances for a family of finite models, with no claim that one fixed model realizes these ratios at every horizon."))),
                DescribeRole.Theorem))));
}
