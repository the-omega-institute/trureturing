using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenSplitSufficientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/GoldenSplitSufficient",
            "Prime splitting and inertia in the golden integers are classified by residue classes modulo five."),
        H("Golden Prime Splitting"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("five-is-a-square-modulo-an-odd-prime-exactly-in-the-square-classes-modulo-five"),
                H("Quadratic-residue criterion"),
                LeanTheorem("D5/S3/Arith/GoldenSplitSufficient.five_is_square_mod_prime_iff_mod_five_eq_one_or_four"),
                Disp(Seq(Forall, Sp, F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Sp, Land, Sp,
                    F.Id("p"), Neq, D(5), Sp, Land, Sp, F.Id("p"), Neq, D(2), Sp, Rightarrow, Sp,
                    Open, Operatorname, Grp(F.Id("IsSquare")), Open, D(5), Sp, Colon, Sp, Operatorname, Grp(F.Id("ZMod")), Sp, F.Id("p"), Close,
                    Sp, Leftrightarrow, Sp, F.Id("p"), Equiv, Pm, D(1), Esc, Open, Operatorname, Grp(F.Id("mod")), Sp, D(5), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every natural prime p distinct from both five and two, five is a square in ZMod p if and only if p is congruent to one or minus one modulo five. The exclusion of two is explicit because five is a square modulo two although two belongs to a nonsquare residue class modulo five.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("split-primes-are-exactly-plus-or-minus-one-modulo-five"),
                H("Split-prime criterion"),
                LeanTheorem("D5/S3/Arith/GoldenSplitSufficient.golden_not_prime_iff_mod_five_eq_one_or_four"),
                Disp(Seq(Forall, Sp, F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Sp, Land, Sp, F.Id("p"), Neq, D(5), Sp, Rightarrow, Sp,
                    Open, Neg, Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Sp, Colon, Sp, Operatorname, Grp(F.Id("GoldenInt")), Close,
                    Sp, Leftrightarrow, Sp, F.Id("p"), Equiv, Pm, D(1), Esc, Open, Operatorname, Grp(F.Id("mod")), Sp, D(5), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every natural prime p other than five, its image fails to remain prime in the golden integers exactly when p is congruent to one or minus one modulo five. Failure to remain prime is the formal splitting predicate used here.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("inert-primes-are-exactly-plus-or-minus-two-modulo-five"),
                H("Inert-prime criterion"),
                LeanTheorem("D5/S3/Arith/GoldenSplitSufficient.golden_prime_iff_mod_five_eq_two_or_three"),
                Disp(Seq(Forall, Sp, F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Close, Sp, Land, Sp, F.Id("p"), Neq, D(5), Sp, Rightarrow, Sp,
                    Open, Operatorname, Grp(F.Id("Prime")), Open, F.Id("p"), Sp, Colon, Sp, Operatorname, Grp(F.Id("GoldenInt")), Close,
                    Sp, Leftrightarrow, Sp, Open, F.Id("p"), Equiv, D(2), Sp, Lor, Sp, F.Id("p"), Equiv, D(3), Close,
                    Esc, Open, Operatorname, Grp(F.Id("mod")), Sp, D(5), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every natural prime p other than five, its image remains prime in the golden integers exactly when p is congruent to two or three modulo five, equivalently plus or minus two modulo five.")))
            ))));
}
