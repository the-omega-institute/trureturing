using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class TemporalFiberCanonicalKernelBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive finite spectral time fibers are exactly the canonical "
            + "future-readout kernels.",
        H("Temporal Fiber Canonical-Kernel Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("temporal-range-kernel-eq-observation-setoid"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/TemporalFiberCanonicalKernelBridge.temporal_range_kernel_eq_observation_setoid"),
                H("Consecutive temporal fibers reuse the canonical observation kernel"),
                StatementSource.FromAuthor(KernelBridgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The equality kernel of the spectral readout on times zero through the selected depth is the repository's canonical observation setoid at that depth.")),
                    Paragraph(Text(
                        "The proof identifies the finite spectral word with futureReadoutWord and introduces no parallel time-kernel hierarchy."))),
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

    private static Formula KernelBridgeFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("m"), Comma, Sp, F.Id("d"), Colon,
        RowBreak, Grp(),
        Call("ker",
            Call("temporalWindowReadout", F.Id("m"),
                Call("range", Seq(F.Id("d"), Sp, Plus, Sp, D(1))))),
        Sp, Eq, Sp,
        Call("observationSetoid",
            Call("oneStepSpectralUpdate", F.Id("m")),
            Call("modalSumReadout"), F.Id("d")), Dot,
        End, Grp(F.Id("gathered"))));

}
