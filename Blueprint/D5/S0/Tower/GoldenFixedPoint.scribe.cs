using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class GoldenFixedPointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real golden ratio satisfies the reciprocal fixed-point equation.",
        H("Golden Reciprocal Fixed Point"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-ratio-reciprocal-fixed-point"),
                DeclarationHandle.Create(
                    "D5/S0/Tower/GoldenFixedPoint.golden_ratio_reciprocal_fixed_point"),
                H("The golden ratio is a reciprocal fixed point"),
                StatementSource.FromAuthor(Disp(Seq(
                    Varphi, Sp, Eq, Sp, D(1), Sp, Plus, Sp,
                    Frac, Grp(D(1)), Grp(Varphi)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The equation is an arithmetic instance of the fixed-point clause in " +
                        "the source atom. It is obtained directly from the library's exact " +
                        "golden-ratio reciprocal and conjugate identities.")),
                    Paragraph(Text(
                        "This is an honest partial closure of that one equation only. The " +
                        "source's combinator, diagonal, representability, convergence, and " +
                        "self-application readings remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
