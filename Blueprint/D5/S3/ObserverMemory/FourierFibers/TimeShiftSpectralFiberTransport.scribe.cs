using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class TimeShiftSpectralFiberTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Time translation becomes diagonal multiplication on spectral fibers and "
            + "obeys an exact semigroup law.",
        H("Time-Shift Spectral Fiber Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("crystal-time-sample-after-transport"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/TimeShiftSpectralFiberTransport.crystal_time_sample_after_transport"),
                H("Transported readout equals translated time"),
                StatementSource.FromAuthor(TransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Diagonal transport through a finite number of steps followed by a time readout equals reading the original amplitudes at the translated time.")),
                    Paragraph(Text(
                        "The theorem is an exact semigroup identity for finite modal fibers. It supplies the typed bridge between time shifts and spectral multiplication."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula TransportFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("m"), Comma, Sp, F.Id("a"), Comma, Sp,
        F.Id("t"), Comma, Sp, F.Id("s"), Colon,
        RowBreak, Grp(),
        Call("crystalTimeSample", F.Id("m"),
            Call("spectralFiberTransport", F.Id("m"), F.Id("s"),
                F.Id("a")), F.Id("t")),
        Sp, Eq, Sp,
        Call("crystalTimeSample", F.Id("m"), F.Id("a"),
            Seq(F.Id("s"), Sp, Plus, Sp, F.Id("t"))), Dot,
        End, Grp(F.Id("gathered"))));

}
