using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class SymmetryBreakingObservabilityGainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Splitting a two-mode degeneracy converts a persistent hidden fiber into a faithful two-sample observer.",
        H("Symmetry-Breaking Observability Gain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("symmetry-breaking-observability-gain"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/SymmetryBreakingObservabilityGain.symmetry_breaking_observability_gain"),
                H("Mode splitting increases observability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An exactly degenerate two-mode system has a nontrivial all-time hidden direction, whereas distinct split multipliers make the first two time samples injective.")),
                    Paragraph(Text(
                        "The theorem captures an information gain caused by lifting spectral degeneracy. It is a finite observer statement and does not assign a physical mechanism to the split."))),
                DescribeRole.Theorem))));
}
