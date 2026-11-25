using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class CompleteHockeyStickBasisSupportDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A condition on computational basis outputs forces unit complete hockey-stick contraction.",
        H("Complete hockey-stick contraction and basis output support"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-hockey-stick-basis-support"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStickBasisSupport.result"),
            H("Trivial intersection of the basis output supports"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Consider a finite channel with at least two computational basis states. If "
                    + "the intersection of their output supports is zero, its complete hockey-stick "
                    + "contraction coefficient is one at every fixed parameter greater than one.")),
                Paragraph(Text(
                    "A simplex of reference vectors makes differences between the prepared supports "
                    + "injective. A left inverse gives a measurement effect that annihilates the "
                    + "negative output terms. Its compression on the distinguished reference "
                    + "coordinate approaches the identity. Positive input blocks are calibrated to "
                    + "give two density states with the same reference marginal. The input divergence "
                    + "and the tested output divergence have the same normalization, so their ratio "
                    + "approaches one using a reference of input dimension.")),
                Paragraph(Text(
                    "The simplex construction follows the common-support argument of Lluis Eriksson, "
                    + "Common support and complete contraction with quantum side information, v3, "
                    + "Section 6. The proof here uses an explicit hockey-stick difference at a fixed "
                    + "parameter and applies to any channel with the stated basis output supports."))),
            DescribeRole.Theorem))));
}
