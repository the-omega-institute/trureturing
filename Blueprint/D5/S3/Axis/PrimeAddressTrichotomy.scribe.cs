using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class PrimeAddressTrichotomyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every prime is either two or has residue one or three modulo four.",
        H("Prime Residues Modulo Four"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-address-mod-four-trichotomy"),
                DeclarationHandle.Create(
                    "D5/S3/Axis/PrimeAddressTrichotomy.prime_address_mod_four_trichotomy"),
                H("A prime is two or has residue one or three modulo four"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("p"), Sp, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("Prime"), Open, F.Id("p"), Close, Sp,
                    Rightarrow, Sp,
                    F.Id("p"), Sp, Eq, Sp, Num(2), Sp,
                    Lor, Sp,
                    new Formula.Modulo(F.Id("p"), D(4)), Sp, Eq, Sp, Num(1), Sp,
                    Lor, Sp,
                    new Formula.Modulo(F.Id("p"), D(4)), Sp, Eq, Sp, Num(3), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural prime p, either p is the even prime 2, or its remainder "
                        + "after division by 4 is 1 or 3. These alternatives are exhaustive; the last "
                        + "two alternatives are the odd residue classes modulo 4.")),
                    Paragraph(Text(
                        "This records only the prime-residue trichotomy clause. The separate equivalence "
                        + "between residue 1 modulo 4 and representation as a sum of two squares, and the "
                        + "dynamical classifier interpretation, remain unresolved and are not claimed here.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. The Lean theorem directly combines "
                        + "Nat.Prime.eq_two_or_odd with Nat.odd_mod_four_iff; no complete trichotomy wrapper "
                        + "was found under the queried names."))),
                DescribeRole.Theorem)),
        []));
}
