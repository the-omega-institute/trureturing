using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class PrimeZeckendorfTemporalizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/FourierFibers/PrimeZeckendorfTemporalization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive heat time preserves calibrated prime identity, while wrapped phase time "
            + "has arbitrarily late finite-channel near-recurrence.",
        H("Prime-Zeckendorf Temporalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("first-excited-heat-multiplier-injective"),
                DeclarationHandle.Create(
                    Prefix + "first_excited_heat_multiplier_injective"),
                H("Positive heat time preserves prime identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("t"), Colon, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("t"), Sp, Rightarrow, RowBreak, Grp(),
                    Operatorname, Grp(F.Id("Injective")),
                    Open,
                    Operatorname, Grp(F.Id("firstExcitedHeatMultiplier")),
                    Open, F.Id("t"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The real exponential is injective and positive time leaves a nonzero "
                            + "frequency scale. Equality of heat multipliers therefore reduces "
                            + "to equality of the calibrated first golden frequencies and then "
                            + "to equality of prime channels.")),
                    Paragraph(Text(
                        "The same module transports the existing finite prime-phase recurrence "
                            + "through the phi-squared first-mode scaling. Thus the oscillatory "
                            + "phase observer can return arbitrarily close to coherence at late "
                            + "times even though the dissipative heat observer remains faithful."))),
                DescribeRole.Theorem))));
}
