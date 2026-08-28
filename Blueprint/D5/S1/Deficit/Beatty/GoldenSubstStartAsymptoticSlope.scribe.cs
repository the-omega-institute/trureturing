using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Beatty;

internal sealed class GoldenSubstStartAsymptoticSlopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The substitution-start ratios converge to the golden ratio.",
        H("Golden Substitution-Start Asymptotic Slope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-substitution-start-asymptotic-slope"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/Beatty/GoldenSubstStartAsymptoticSlope."
                        + "golden_subst_start_asymptotic_slope"),
                H("The substitution-start sequence has golden asymptotic slope"),
                StatementSource.FromAuthor(Disp(Call(
                    "Tendsto",
                    Seq(
                        Open,
                        Open, F.Id("v"), Sp, Colon, Sp, Mathbb, Grp(F.Id("N")), Close,
                        Sp, Mapsto, Sp,
                        Frac,
                        Grp(Open, Operatorname, Grp(F.Id("goldenSubstStart")),
                            Open, F.Id("v"), Close, Sp, Colon, Sp,
                            Mathbb, Grp(F.Id("R")), Close),
                        Grp(Open, F.Id("v"), Sp, Colon, Sp,
                            Mathbb, Grp(F.Id("R")), Close),
                        Close),
                    F.Id("atTop"),
                    Call("nhds", Varphi)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For natural indices tending to infinity, the real ratio of the "
                            + "substitution-block start to its index tends to the golden ratio. "
                            + "This is a slope statement about substitution positions, not a "
                            + "counting density.")),
                    Paragraph(Text(
                        "Unfolding goldenSubstStart gives the index plus the prefix true-letter "
                            + "count. The merged true-letter density tends to the inverse golden "
                            + "ratio, and the identity 1 + phi^-1 = phi gives the stated limit. "
                            + "The ratio rewrite is used only eventually, at positive indices."))),
                DescribeRole.Theorem))));
}
