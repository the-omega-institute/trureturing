using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.NamingRate;

internal sealed class TransparencyAsymptoticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The transparency of the Massar-Popescu naming rate is asymptotic to one over the sample count.",
        H("Naming Rate Transparency Asymptotic"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("naming-rate-transparency-is-asymptotic-to-one-over-n"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/NamingRate/TransparencyAsymptotic.naming_rate_transparency_asymptotic"),
                H("The scaled naming-rate transparency tends to one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                    F.Id("n"), Left, Open,
                    D(1), Minus,
                    Frac, Grp(F.Id("n"), Plus, D(1)), Grp(F.Id("n"), Plus, D(2)),
                    Right, Close, Sp, Eq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the naming rate F(n) = (n + 1) / (n + 2), the transparency is "
                        + "1 - F(n). Multiplying it by n gives a sequence tending to one, which "
                        + "states precisely that the transparency decays asymptotically as 1 / n.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies tendsto_natCast_div_add_atTop. The Lean proof "
                        + "rewrites the scaled transparency to n / (n + 2) and applies that theorem "
                        + "directly, without reproving the library limit.")),
                    Paragraph(Text(
                        "This deposit closes only the naming-rate asymptotic sentence in source "
                        + "remark 27.759 clause 2. The entropy closed forms and the interpretation "
                        + "of the N = 1 value in the same clause remain outside this closure."))),
                DescribeRole.Theorem)),
        []));
}
