using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class GoldenPowerRoundingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The second and third golden powers have exact adjacent integer rounding pairs.",
        H("Rounding the Second and Third Golden Powers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-power-floor-ceil-pairs"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/GoldenPowerRounding.golden_power_floor_ceil_pairs"),
                H("Golden-power floor and ceiling pairs"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lfloor, Varphi, Caret, Grp(D(3)), Rfloor, Sp, Eq, Sp, D(4),
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("ceil")), Open,
                    Varphi, Caret, Grp(D(3)), Close, Sp, Eq, Sp, D(5),
                    Sp, Land, Sp,
                    Lfloor, Varphi, Caret, Grp(D(2)), Rfloor, Sp, Eq, Sp, D(2),
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("ceil")), Open,
                    Varphi, Caret, Grp(D(2)), Close, Sp, Eq, Sp, D(3)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Pinned Mathlib supplies the golden-ratio quadratic identity, its "
                        + "strict bounds between one and two, and the exact floor and ceiling "
                        + "characterizations. These facts give the four adjacent integer "
                        + "rounding values directly.")),
                    Paragraph(Text(
                        "This partial closure covers only the explicit rounding clause. The "
                        + "fiber-support interval, its distribution word, and the frequency "
                        + "claims remain outside this declaration."))),
                DescribeRole.Theorem))));
}
