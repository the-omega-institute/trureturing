using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class FermatLittleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/ArithUnits/FermatLittle",
            "A power one below a prime is congruent to one when the prime does not divide the base."),
        H("Fermat's Little Theorem"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("fermat-little-theorem-for-a-base-not-divisible-by-the-prime"),
                H("A base not divisible by a prime has power p minus one congruent to one"),
                LeanTheorem(
                    "D5/S3/ArithUnits/FermatLittle.fermat_little_theorem"),
                Disp(Seq(
                    Forall, Sp, F.Id("p"), Comma, F.Id("a"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("p"), Esc, F.Text, Grp(F.Id("prime")), Sp, Land, Sp,
                    Neg, Open, F.Id("p"), Sp, Mid, Sp, F.Id("a"), Close,
                    Sp, Rightarrow, Sp,
                    F.Id("a"), Caret, Grp(F.Id("p"), Minus, D(1)),
                    Sp, Equiv, Sp, D(1), Esc,
                    Open, Operatorname, Grp(F.Id("mod")), Esc, F.Id("p"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For every natural prime p and natural base a, if p does not divide a, "
                        + "then a raised to p minus one is congruent to one modulo p. The explicit "
                        + "primality and nondivisibility premises preserve the source atom's full "
                        + "scope, and the conclusion is an exact natural-number modular congruence.")),
                    Paragraph(Text(
                        "Pinned Mathlib already proves the congruence from coprimality as "
                        + "Nat.ModEq.pow_card_sub_one_eq_one. Its theorem "
                        + "Nat.Prime.coprime_iff_not_dvd converts the stated nondivisibility "
                        + "premise to that library hypothesis. The Lean declaration is therefore "
                        + "a thin repository-addressed wrapper, not a reproof of the classical "
                        + "permutation argument recorded with the source atom. No numerical "
                        + "certificate is asserted.")))
            ))));
}
