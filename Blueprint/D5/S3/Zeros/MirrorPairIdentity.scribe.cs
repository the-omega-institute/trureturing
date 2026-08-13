using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class MirrorPairIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Applying reflected conjugation twice returns the original complex coordinate.",
        H("Mirror-Pair Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflected-conjugation-is-an-involution"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/MirrorPairIdentity.mirror_pair_involution"),
                H("Reflected conjugation is an involution"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Rho, InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc,
                    D(1), Sp, Minus, Sp,
                    Overline, Grp(D(1), Sp, Minus, Sp, Overline, Grp(Rho)),
                    Sp, Eq, Sp, Rho))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every complex coordinate rho, applying the map "
                        + "rho maps to 1 minus its conjugate twice returns rho. "
                        + "The result is the algebraic involution underlying mirror-pair "
                        + "arguments; it does not assert that either coordinate is a zeta zero."))),
                DescribeRole.Theorem))));
}
