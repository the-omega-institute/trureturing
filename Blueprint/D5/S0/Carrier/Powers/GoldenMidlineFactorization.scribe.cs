using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier.Powers;

internal sealed class GoldenMidlineFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden midline marker factors into one half and the reciprocal golden square.",
        H("Golden Midline Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-midline-factorization"),
                DeclarationHandle.Create(
                    "D5/S0/Carrier/Powers/GoldenMidlineFactorization"
                    + ".golden_midline_factorization"),
                H("Factorization of the golden midline marker"),
                StatementSource.FromAuthor(Disp(Seq(
                    Frac, Grp(D(1)), Grp(D(2), Times, Varphi, Caret, Grp(D(2))),
                    Sp, Eq, Sp,
                    Open, Frac, Grp(D(1)), Grp(D(2)), Close, Times,
                    Open, Frac, Grp(D(1)), Grp(Varphi, Caret, Grp(D(2))), Close,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Mathlib's generic one_div_mul_one_div identity rewrites the reciprocal "
                        + "of a product as the product of the two reciprocals. Specializing its "
                        + "factors to 2 and the square of the real golden ratio proves the displayed "
                        + "identity without adding a second proof of the generic law.")),
                    Paragraph(Text(
                        "This is a deeper partial closure of the source remark. The conjugation and "
                        + "field-action interpretations, together with the other five source "
                        + "subitems, remain unresolved and are not asserted here."))),
                DescribeRole.Theorem)),
        []));
}
