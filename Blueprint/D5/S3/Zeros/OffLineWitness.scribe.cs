using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class OffLineWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closed off-line zero refutes the universal midline claim.",
        H("Off-Line Witness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("closed-zero-midline-refutation"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/OffLineWitness.closed_zero_midline_refutation"),
                H("A closed off-line zero refutes universal midline location"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source atom says that a closed-zero-only-on-the-midline claim is "
                        + "false when its instrument supplies an off-line closed zero. This "
                        + "partial closure isolates exactly that logical clause: a supplied "
                        + "zero, its closure witness, and its off-line real part contradict the "
                        + "universal location assertion.")),
                    Paragraph(Text(
                        "The declaration is general over the zero predicate, closure predicate, "
                        + "and proposed midline. It constructs no analytic zero and assumes no "
                        + "properties beyond the three displayed witness hypotheses.")),
                    Paragraph(Text(
                        "The source's separate necessity claim about multiplicativity or derived "
                        + "positivity is not formalized here and remains unresolved. Pinned "
                        + "Mathlib contained the generic negation lemmas but no closed-zero "
                        + "midline theorem; the proof specializes the disputed universal claim "
                        + "to the supplied witness."))),
                DescribeRole.Theorem)),
        []));
}
