using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.FloorCounts;

internal sealed class RotationEventCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Floor-difference rotation events telescope and have discrepancy strictly below one.",
        H("Rotation Event Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bounded-rotation-event-count"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/FloorCounts/RotationEventCount.bounded_event_count"),
                H("Bounded rotation event count"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("bounded"), Sp, F.Id("event"), Sp, F.Id("count")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The event weight is the difference of consecutive floor samples "
                        + "along a real rotation. Summing over a finite window telescopes to "
                        + "the endpoint floor difference, and the resulting count differs "
                        + "from the real displacement by strictly less than one.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. The proof uses the "
                        + "existing Int.floor_add_fract, Int.fract_nonneg, and Int.fract_lt_one "
                        + "lemmas, together with ring and linear arithmetic; no floor or "
                        + "equidistribution theorem is reproved. The formal scope is the "
                        + "finite event-count identity and its unit discrepancy bound."))),
                DescribeRole.Theorem))));
}
