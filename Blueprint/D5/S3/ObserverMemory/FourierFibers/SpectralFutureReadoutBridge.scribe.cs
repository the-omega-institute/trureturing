using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class SpectralFutureReadoutBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite spectral time-delay word is exactly the repository's "
            + "canonical future-readout word for diagonal modal transport.",
        H("Spectral Future-Readout Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("future-readout-word-eq-crystal-time-word"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/SpectralFutureReadoutBridge.future_readout_word_eq_crystal_time_word"),
                H("Spectral delays reuse the canonical future word"),
                StatementSource.FromAuthor(BridgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For one-step diagonal spectral evolution and the modal-sum sensor, the repository's canonical finite future-readout word equals the finite crystal time word coordinatewise.")),
                    Paragraph(Text(
                        "This bridge prevents a second delay-coordinate API and connects finite Koopman-style time-delay reasoning to the existing observer-completion machinery."))),
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

    private static Formula BridgeFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, F.Id("m"), Comma, Sp, F.Id("d"), Comma, Sp,
        F.Id("a"), Colon,
        RowBreak, Grp(),
        Call("futureReadoutWord",
            Call("oneStepSpectralUpdate", F.Id("m")),
            Call("modalSumReadout"), F.Id("d"), F.Id("a")),
        Sp, Eq, Sp,
        Call("crystalTimeWord", F.Id("m"), F.Id("d"), F.Id("a")), Dot,
        End, Grp(F.Id("gathered"))));

}
