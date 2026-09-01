using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class TimeShiftSpectralFiberTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Time translation becomes diagonal multiplication on finite spectral fibers.",
        H("Time-Shift Spectral Fiber Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("crystal-time-sample-after-transport"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/TimeShiftSpectralFiberTransport.crystal_time_sample_after_transport"),
                H("Transported readout equals translated time"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Diagonal transport through a finite number of steps followed by a time readout equals reading the original amplitudes at the translated time.")),
                    Paragraph(Text(
                        "The theorem is an exact semigroup identity for finite modal fibers. It supplies the typed bridge between time shifts and spectral multiplication."))),
                DescribeRole.Theorem))));
}
