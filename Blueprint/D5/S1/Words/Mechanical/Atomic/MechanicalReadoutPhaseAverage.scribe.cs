using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical.Atomic;

internal sealed class MechanicalReadoutPhaseAverageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform phase averaging of the numbered atomic measure is Lebesgue measure on the unit interval.",
        H("Mechanical Readout Phase Average"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mechanical-atomic-phase-average"),
                DeclarationHandle.Create("D5/S1/Words/Mechanical/Atomic/MechanicalReadoutPhaseAverage.geometric_atomic_phase_average"),
                H("Uniform phase average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every measurable subset of [0,1], integrating the actual numbered atomic measure over phases in [0,1) gives its Lebesgue measure. Each level partitions (0,1] into equal cells under its threshold maps; the geometric mass identity then sums the cell contributions to one. The statement uses the half-open phase domain of the mechanical word and allows arbitrary measurable sets within the closed unit interval."))),
                DescribeRole.Theorem))));
}
