using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Equivariance;

internal sealed class EquivariantExposureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single value determines an equivariant map on a transitive group action.",
        H("Equivariant Exposure on a Transitive Action"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("equivariant-maps-are-exposed-by-one-value"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Equivariance/EquivariantExposure."
                    + "equivariant_maps_eq_of_eq_at"),
                H("One value determines an equivariant map"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Transitive")), Open,
                    F.Id("G"), Comma, Sp, F.Id("X"), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Equivariant")), Open, F.Id("f"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Equivariant")), Open, F.Id("g"), Close,
                    Sp, Land, Sp,
                    F.Id("f"), Open, F.Id("x"), Underscore, Grp(D(0)), Close,
                    Sp, Eq, Sp,
                    F.Id("g"), Open, F.Id("x"), Underscore, Grp(D(0)), Close,
                    Sp, Rightarrow, Sp, F.Id("f"), Sp, Eq, Sp, F.Id("g"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any target point, pretransitivity supplies a group element that "
                        + "moves the chosen base point to that target. Equivariance transports "
                        + "the base-point equality along this group element, so the two maps "
                        + "agree at every point.")),
                    Paragraph(Text(
                        "The proof reuses Mathlib's isPretransitive_iff_base theorem. No "
                        + "finiteness, faithfulness, or action on the codomain beyond a MulAction "
                        + "is required.")),
                    Paragraph(Text(
                        "This is partial closure of the source atom's symmetric-exposure clause: "
                        + "equivariance turns one representative check into a global check. It "
                        + "does not formalize the Delta tax table, probe counterexample, or the "
                        + "gate-to-twist classification stated elsewhere in that atom."))),
                DescribeRole.Theorem))));
}
