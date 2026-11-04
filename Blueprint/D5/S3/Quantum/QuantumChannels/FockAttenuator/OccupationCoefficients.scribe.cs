using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class OccupationCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Occupation coordinates for every completed input.",
        H("Occupation coordinates for every completed input"),
        Blocks(Describe.Lean(DescribeId.Create("completed-fock-occupation-coordinates"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/OccupationCoefficients.occupation_coefficient_of_total"),
            H("Occupation coordinates for every completed input"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every transmissivity in the closed unit interval, every number environment n and every completed Fock input a, the actual output coordinate with total occupation N=i+j is zero when N<n. For N>=n it equals a(N-n) times the frozen finite Fock transition amplitude from input occupation N-n and environment n to output coordinates j,i.")),
                Paragraph(Text("The frozen beamSplitter number-state expansion conserves total occupation. Tensoring with the number environment is the actual continuous single-column embedding. Composing it with the beam unitary and both continuous coordinate evaluations gives a continuous linear functional on the entire input Hilbert space. Equality on every occupation vector extends to every completed input.")),
                Paragraph(Text("The theorem states the exact existing fockExpansion amplitude and includes arbitrary infinite support. The separate closed n=2 binomial and square-root simplification is not asserted here. The physical kernel identity supplies the rank bridge independently of that simplification."))),
            DescribeRole.Theorem))));
}

