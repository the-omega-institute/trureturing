using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class DecoherenceFreezeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The decoherence-freeze deposit is positive exactly above its critical inverse temperature.",
        H("Decoherence-Freeze Critical Temperature Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-freeze-deposit-subtracts-the-temperature-scaled-entropy-tax"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/DecoherenceFreeze.freezeDeposit"),
                H("The freeze deposit subtracts the temperature-scaled entropy tax"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For inverse temperature beta, entropy tax Delta S, and passive-energy shift "
                    + "Delta E pass, the freeze deposit is the passive-energy shift minus the "
                    + "entropy tax divided by beta."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("the-critical-inverse-temperature-is-the-entropy-energy-ratio"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/DecoherenceFreeze.criticalInverseTemperature"),
                H("The critical inverse temperature is the entropy-energy ratio"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The critical inverse temperature is the entropy tax divided by the "
                    + "passive-energy shift."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "the-freeze-deposit-is-positive-exactly-above-the-critical-inverse-temperature"),
                DeclarationHandle.Create("D5/S3/QuantumChannels/DecoherenceFreeze.decoherence_freeze_iff_above_critical"),
                H("The freeze deposit is positive exactly above the critical inverse temperature"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Lt, Beta, Sp, Land, Sp,
                    D(0), Lt, Delta, Sp, F.Id("E"), Underscore, Grp(F.Id("pass")),
                    Sp, Rightarrow, Sp, Open,
                    D(0), Lt, Operatorname, Grp(F.Id("freezeDeposit")), Open,
                    Beta, Comma, Delta, Sp, F.Id("S"), Comma,
                    Delta, Sp, F.Id("E"), Underscore, Grp(F.Id("pass")), Close,
                    Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("criticalInverseTemperature")), Open,
                    Delta, Sp, F.Id("S"), Comma,
                    Delta, Sp, F.Id("E"), Underscore, Grp(F.Id("pass")), Close,
                    Lt, Beta, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When beta and the passive-energy shift are positive, dividing and "
                    + "cross-multiplying preserve strict inequalities. Consequently, positivity "
                    + "of the freeze deposit is equivalent to beta exceeding the critical "
                    + "entropy-energy ratio."))),
                DescribeRole.Theorem))));
}
