using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class GoldenScaleCharacterDeckBlindnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer golden Fourier characters are blind to one full scale deck step "
            + "even though the golden helix level changes.",
        H("Golden Scale Character Deck Blindness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-helix-fourier-readout-not-injective"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/GoldenScaleCharacterDeckBlindness.golden_helix_fourier_readout_not_injective"),
                H("Quotient Fourier readout forgets the helix sheet"),
                StatementSource.FromAuthor(BlindnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "One full golden scale period leaves every integer Fourier character unchanged, although the universal-cover helix level increases.")),
                    Paragraph(Text(
                        "The theorem reuses GoldenScaleHelix to separate quotient phase from completion-depth memory. Adding the level coordinate detects the deck step."))),
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

    private static Formula BlindnessFormula() => Disp(Seq(
        Forall, Sp, F.Id("m"), Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))),
        Comma, Sp,
        Neg, Sp, Call("Injective",
            Call("goldenHelixFourierReadout", F.Id("m"))), Dot));

}
