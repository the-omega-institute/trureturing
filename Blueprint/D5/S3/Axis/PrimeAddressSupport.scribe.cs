using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class PrimeAddressSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonzero finitely supported prime-address motion has a nonempty address.",
        H("Prime Address Support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonzero-prime-address-motion-has-nonempty-support"),
                DeclarationHandle.Create(
                    "D5/S3/Axis/PrimeAddressSupport.nonempty_support_of_ne_zero"),
                H("Nonzero prime-address motions have nonempty support"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Sp, Colon, Sp,
                    Operatorname, Grp(F.Id("PrimeAddressMotion")), Comma, Sp,
                    F.Id("u"), Sp, Neq, Sp, Num(0), Sp,
                    Rightarrow, Sp,
                    Operatorname, Grp(F.Id("Nonempty")), Open,
                    Operatorname, Grp(F.Id("Support")), Open, F.Id("u"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Prime addresses are natural numbers carrying primality certificates. "
                        + "A motion is represented by a finitely supported function on those "
                        + "addresses, so every address in its support is prime by construction.")),
                    Paragraph(Text(
                        "This records only the mathematical support clause of the source atom. "
                        + "The separate repository discipline for changes outside the generated "
                        + "prime ledger is not claimed by this theorem.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. The exact supporting result "
                        + "is Finsupp.support_nonempty_iff, which states that a finitely supported "
                        + "function has nonempty support exactly when it is nonzero. The Lean "
                        + "theorem is a direct wrapper over that library equivalence."))),
                DescribeRole.Theorem)),
        []));
}
