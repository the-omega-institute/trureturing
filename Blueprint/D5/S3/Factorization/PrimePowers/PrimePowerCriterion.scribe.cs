using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.PrimePowers;

internal sealed class PrimePowerCriterionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Apostol =
        LibraryNoteRef.Create("D5/L/apostol1976introduction");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime powers are exactly the natural numbers with a unique prime divisor.",
        H("Prime-Power Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-iff-unique-prime-divisor"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/PrimePowers/PrimePowerCriterion."
                    + "prime_power_iff_unique_prime_divisor"),
                H("A natural number is a prime power exactly when its prime divisor is unique"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("IsPrimePow")), Open, F.Id("n"), Close,
                    Sp, Iff, Sp,
                    Exists, Bang, Sp, F.Id("p"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close,
                    Sp, Land, Sp, F.Id("p"), Sp, Mid, Sp, F.Id("n")))),
                AssessedProvenance.FromLiterature(Apostol),
                Blocks(Paragraph(Text(
                    "For every natural number n, being a positive power of a prime is equivalent "
                    + "to the existence of exactly one prime divisor of n. The edge cases zero "
                    + "and one make both sides false, so the equivalence needs no additional lower "
                    + "bound. Pinned Mathlib supplies the exact characterization "
                    + "isPrimePow_iff_unique_prime_dvd; the Lean theorem is only the thinnest "
                    + "repository-addressed wrapper over that upstream truth. This closes only "
                    + "the arithmetic core of the prime-power criterion in appendix E.148. The "
                    + "geometric-spectrum genealogy, maximal-chain count, cyclotomic mechanism, "
                    + "prime zeta identity, growth constant, Tauberian constant, MUB window, and "
                    + "all numerical certificates in the same atom remain outside this claim."))),
                DescribeRole.Theorem
            ))));
}
