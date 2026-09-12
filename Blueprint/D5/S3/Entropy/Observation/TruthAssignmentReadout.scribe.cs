using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class TruthAssignmentReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite truth-assignment entropy divides into observed and unresolved information.",
        H("Truth Assignment Readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("truth-assignment-entropy-decomposition"),
                DeclarationHandle.Create("D5/S3/Entropy/Observation/TruthAssignmentReadout.truth_assignment_entropy_decomposition"),
                H("Truth Assignment Readout"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The source state assigns a Boolean value to each member of a finite set of question labels. A nonnegative normalized mass supplies its probability law. The question labels are coordinates, not a formalization of all logical propositions or their semantic validity.")),
                    Paragraph(Text("For a deterministic finite readout q, the identity is H(X) = H(q(X)) + H(X given q(X)). If a second readout is a deterministic function of the first, its residual conditional entropy is at least that of the first.")),
                    Paragraph(Text("This is the existing deterministic readout theorem specialized to finite Boolean assignments. The entropy is finite Shannon entropy, and residual uncertainty is relative to the probability law and available readout. No thermodynamic law or metaphysical identity between entropy and truth is asserted."))),
                DescribeRole.Theorem))));
}
