using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class EffectProbabilityExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite additivity on all effects gives a unique density representative.",
        H("Effect probability extension"),
        Blocks(
            Paragraph(Text("Let the interface be any finite complex matrix algebra. A single real-valued function on effects is nonnegative, takes value one at the identity, and is additive whenever the sum is an effect. No scalar homogeneity or continuity is assumed. Values outside the effect interval are immaterial.")),
            Paragraph(Text("Equal finite subdivision gives rational homogeneity. Monotonicity and rational approximation give real homogeneity on the unit interval. Scaling each positive matrix into the effect interval defines a positive-cone functional; comparison at a common scale proves independence of scale and additivity.")),
            Paragraph(Text("The positive and negative parts of a Hermitian matrix define its real-linear extension. Equality of two differences is equality of cross sums, which proves well-definedness. Real and imaginary Hermitian parts then give the complex-linear extension. Existing trace-dual positivity represents this functional by a positive matrix. Normalization gives trace one, and the effect span gives uniqueness.")),
            Paragraph(Text("This converse includes dimension two. It supplies the probability representation assumed by the finite-instrument application; neither static event structure nor positive history length implies its probability hypotheses. Busch supplies the mathematical source, while the finite-dimensional construction uses only binary additivity.")),
            Describe.Lean(
                DescribeId.Create("effect-density-representation"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/EffectProbabilityExtension.effect_density_representation"),
                H("Unique density representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/busch2003effectprobabilities")),
                Blocks(Paragraph(Text("Every nonnegative normalized finitely additive probability on all effects is the trace pairing with exactly one positive trace-one matrix. The construction and uniqueness preserve arbitrary finite interface dimension."))),
                DescribeRole.Theorem))));
}
