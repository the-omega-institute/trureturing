using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold.TwiningTrace;

internal sealed class P48qCubicOscillatorTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The neutral Sugawara grade trace of the native P48q order-three lift counts sixteen-coloured occupations.",
        H("The P48q Cubic Oscillator Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("neutral-grade-fixed-occupations"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/Orbifold/TwiningTrace/"
                    + "P48qCubicOscillatorTrace.standardOscillatorTrace_eq_occupationCount"),
                H("The trace counts occupations constant on current cycles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The complex current space of P48q has sixteen basis triples cyclically permuted by the Nebe isometry. The change to these coordinates preserves each current frequency, so the monomials of energy n give a basis for the actual charge-zero Sugawara eigenspace. The native lift has phase one there and permutes this basis.")),
                    Paragraph(Text("A diagonal entry contributes one exactly when all three occupations in each current cycle agree at every frequency. Retaining one entry from each cycle gives a sixteen-coloured occupation. Repeating it three times triples its energy. Thus the trace at integer energy n is the number of these occupations of energy n/3 when n is a nonnegative multiple of three, and is zero otherwise."))),
                DescribeRole.Theorem),
            Paragraph(Text("On any finite charge set invariant under the isometry, the native lift carries each charge sector into the sector of its image. Only fixed charges contribute to the trace, and each has phase one. The fixed-charge formula therefore sums the neutral trace at energy n minus the charge energy over the fixed charges in the set.")))));
}
