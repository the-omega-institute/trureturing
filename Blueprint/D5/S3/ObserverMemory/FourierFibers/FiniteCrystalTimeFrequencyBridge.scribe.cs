using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class FiniteCrystalTimeFrequencyBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct finite crystal modes are exactly reconstructible from an "
            + "equally long scalar time window.",
        H("Finite Crystal Time-Frequency Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("first-crystal-time-window-injective"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/FiniteCrystalTimeFrequencyBridge.first_crystal_time_window_injective"),
                H("Separated modes are recovered from time samples"),
                StatementSource.FromAuthor(InjectivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finitely many distinct modal multipliers, the first matching number of scalar time samples uniquely recovers all modal amplitudes.")),
                    Paragraph(Text(
                        "This is a finite diagonal spectral realization of Vandermonde tomography. It does not construct an infinite Bloch bundle or identify the sampling index with physical time."))),
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

    private static Formula InjectivityFormula() => Disp(Seq(
        Forall, Sp, F.Id("omega"), Comma, Sp,
        Call("Injective", F.Id("omega")), Sp, Rightarrow, Sp,
        Call("Injective",
            Call("firstCrystalTimeWindow", F.Id("omega"))), Dot));

}
