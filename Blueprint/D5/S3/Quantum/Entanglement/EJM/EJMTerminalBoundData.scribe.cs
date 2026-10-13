using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMTerminalBoundDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMTerminalBoundData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual EJM terminal events, proposed transport witnesses and executable checks.",
        H("The original complete row remains the object of every terminal check"),
        Blocks(
            Paragraph(Text("The data stores one proposed coordinate/outcome action and contraction-representative index for each of the 4588 triangle and 1192 singleton terminal events. Terminal events are decoded from the original local row data, while proposed witnesses come from separate literal integer dictionaries. The check definitions test exact event identity, exact tail transport and the scaled lower-bound comparison. Defining these checks does not prove they return true. All terminal checks and every row tag require complete kernel acceptance receipts, and all proposed contraction integers require their separate original-function equalities before terminal-bound soundness yields a centered-score inequality.")),
            Node("raw-hash", "rawHash", "Read the hash from either original raw row constructor",
                "The same hash field is returned from a terminal or branch raw row. This field is data; its relationship to a complete-row rule is checked by the terminal and tag consumers."),
            Node("triangle-event", "triangleTerminalEvent", "The actual triangle terminal event",
                "For an index in Fin 4588, the event comes from the hash of the corresponding original ten-coordinate triangle raw row, using the original total event decoder."),
            Node("triangle-witness", "triangleWitness", "The actual proposed triangle transport witness",
                "The stored integer is decoded into a local action and a Fin 95 contraction representative. These are untrusted proposals until the exact tail equality is checked."),
            Node("triangle-check", "triangleTerminalCheck", "Executable triangle terminal acceptance test",
                "A split rule rejects. A complete rule checks that its original event equals the decoded terminal event, that its seven-tail transforms exactly to the proposed contraction representative, and that its actual scaled lower bound is at most 256 times F1 at that event minus the proposed contraction integer. Correctness of that contraction integer is a separate premise."),
            Node("triangle-tag", "triangleTerminalTagCheck", "Executable triangle complete-event tag check",
                "Every complete row must have an index below 4588 and its actual event must equal the corresponding literal terminal event. A split row returns true because this tag check asserts no terminal inequality for it."),
            Node("singleton-event", "singletonTerminalEvent", "The actual singleton terminal event",
                "For an index in Fin 1192, the event is decoded from the corresponding original nine-coordinate singleton raw row."),
            Node("singleton-witness", "singletonWitness", "The actual proposed singleton transport witness",
                "The literal witness dictionary decodes into an actual local action and a Fin 332 contraction representative. The downstream checker, rather than the producer, establishes the exact tail match."),
            Node("singleton-check", "singletonTerminalCheck", "Executable singleton terminal acceptance test",
                "The check retains original complete-event identity and exact eight-tail transport. Its integer comparison is the actual row lower bound at most 256 times F2 minus 64 times the proposed contraction integer, preserving the singleton centered-score factor."),
            Node("singleton-tag", "singletonTerminalTagCheck", "Executable singleton complete-event tag check",
                "Every singleton complete row must lie in the first 1192 rows and equal its decoded terminal event. This whole-row tag test supplies an exact event-identification premise; it does not itself validate a numerical bound."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
