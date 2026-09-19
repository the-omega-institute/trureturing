using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape.PhysicalParser;

internal sealed class CellRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identity and erasure distinguish laws of the physical parser's Boolean tape cells.",
        H("Physical parser cell observations"),
        Blocks(
            Paragraph(Text(
                "A tape cell has one of two Boolean values. A readout maps this value to an "
                + "observed Boolean value. The laws below vary this readout on the specified "
                + "output cells while keeping the machine, its initial configuration, control "
                + "states and head coordinates fixed. The identity readout gives exactly the "
                + "full parser laws, including their hypotheses, time bounds and intermediate frames.")),
            Node("observeCells", "Apply a readout to every cell of an output configuration, retaining its control state and head coordinates."),
            Node("erased", "The constant-false readout sends both Boolean values to false, losing every true cell."),
            Paragraph(Text(
                "Coupled rewind. The home cells on pair seven are false and true respectively, "
                + "and both tracks carry true marks at each positive position through the width. "
                + "The initial displacement is bounded by both that width and the frame bound. "
                + "After five times the displacement plus two steps, the machine reaches the first "
                + "padding phase with all three moving heads at zero. Every intermediate frame "
                + "preserves every cell and the other heads; the moving heads remain ordered, "
                + "nonnegative and within the bound, with skew at most one. The readout is applied "
                + "to the terminal memory. Identity satisfies this law by coupled_source_rewind.")),
            Paragraph(Text(
                "Tally. For arbitrary memory, heads, source count, binary counter value and "
                + "continuation, the counting phase increments both the source count and the "
                + "counter, resets the local offset to zero and resumes the continuation. The "
                + "run takes at most eight times the initial counter's bit length plus fourteen "
                + "steps, and its frame holds at every time through termination. The readout "
                + "observes the complete incremented output memory. Identity satisfies this law "
                + "by count_one.")),
            Paragraph(Text(
                "Padding. For any of the six fields and any bit list whose length is at most "
                + "the prescribed width, the padding phase appends enough false bits to reach "
                + "that width, resets the local offset to zero and passes to the next phase. "
                + "It takes at most fourteen times the width plus eleven steps. Its frame holds "
                + "throughout the run, for arbitrary surrounding memory and head positions. "
                + "The readout observes the entire padded output memory. Identity satisfies "
                + "this law by pad_one.")),
            Paragraph(Text(
                "Field parsing. Starting at a source offset, the raw source cells contain a "
                + "block of true bits of payload length, a false delimiter and the payload. "
                + "The offset plus twice the payload length plus one is at most the source "
                + "bound. For any of the six fields, parsing from an empty buffer advances the "
                + "source offset by this encoded length, stores the reversed payload, resets "
                + "the local offset to zero and passes to the next phase. The time is at most "
                + "the product of the encoded length and the sum of eight times the source "
                + "bound and twenty, followed by two further steps. The full field frame "
                + "holds at every intermediate time. The readout "
                + "observes the resulting memory. Identity satisfies this law by parse_field.")),
            Paragraph(Text(
                "Complete execution. The law includes the full six-field contract: positive "
                + "uniform time and space constants and all six positive inputs, with twice "
                + "the first input less than the second and twice the third less than the fourth. "
                + "It asserts the exact return configuration, a quadratic time bound in the "
                + "source length plus one and a linear charge bound in that same quantity at "
                + "every time through return. Every intermediate head lies between zero and "
                + "the source length plus three; each input is less than two raised to the "
                + "source length plus one. It also includes uniqueness of an integer address whenever its framed "
                + "description is a prefix of another. For every Boolean preword and every "
                + "time, the source companion head stays at zero and the raw source track "
                + "equals its initial cells. Only this last cell equality receives the varying "
                + "readout. Identity satisfies the entire conjunction by parser_frame_resources.")),
            Paragraph(Text(
                "Erasure fails each law. For rewind, take zero displacement and a memory whose "
                + "cell value is the track's Boolean coordinate. The preserved true cell then "
                + "disagrees with the erased terminal memory. For tally and padding, an initially "
                + "true source companion cell is preserved by the terminal frame but erased by "
                + "the proposed observation. For field parsing, an empty payload with a false "
                + "source delimiter and a true companion cell gives the same contradiction. "
                + "For complete execution, a one-bit true preword already contradicts erasure "
                + "at time zero. Thus replacing identity by erasure changes whether each full "
                + "law holds. There is exactly one varying readout slot and no anchor slots.")),
            Paragraph(Text(
                "These observations distinguish identity from erasure on the actual tape "
                + "cells. They do not determine a subsequent residual or establish its "
                + "emptiness; that further question remains open."))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/Coding/PhysicalParserExecution")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates"))]));

    private static DocumentBlock Node(string declaration, string text) => Describe.Lean(
        DescribeId.Create(declaration.ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/PhysicalParser/CellRegistrations." + declaration),
        H(declaration),
        StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))),
        DescribeRole.Definition);
}
