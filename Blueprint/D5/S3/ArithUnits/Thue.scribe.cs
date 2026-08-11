using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class ThueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/ArithUnits/Thue",
            "A nonzero residue modulo a prime has nonzero numerator and denominator representatives bounded by the square root."),
        H("Thue's Small-Representative Lemma"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("thue-small-nonzero-representatives-modulo-a-prime"),
                H("A nonzero residue has square-root-bounded numerator and denominator"),
                LeanTheorem("D5/S3/ArithUnits/Thue.thue_small_representatives"),
                Disp(Seq(
                    Forall, Sp, F.Id("p"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Quad, Sp,
                    F.Id("p"), Esc, F.Text, Grp(F.Id("prime")), Comma, Quad, Sp,
                    Forall, Sp, F.Id("x"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Quad, Sp,
                    Neg, Open, F.Id("p"), Sp, Mid, Sp, F.Id("x"), Close,
                    Sp, Rightarrow, Sp, Exists, Sp,
                    F.Id("a"), Comma, F.Id("b"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Quad, Sp,
                    F.Id("a"), Neq, D(0), Sp, Land, Sp, F.Id("b"), Neq, D(0), Sp,
                    Land, Sp, Lvert, Sp, F.Id("a"), Rvert, Leq, Lfloor, Sqrt,
                    Grp(F.Id("p")), Rfloor, Sp,
                    Land, Sp, Lvert, Sp, F.Id("b"), Rvert, Leq, Lfloor, Sqrt,
                    Grp(F.Id("p")), Rfloor, Sp,
                    Land, Sp, F.Id("a"), Equiv, Sp, F.Id("x"), F.Id("b"), Esc,
                    Open, Operatorname, Grp(F.Id("mod")), Esc, F.Id("p"), Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let t be the integer floor of the square root of the prime p. The "
                        + "(t+1)^2 pairs (u,v) with both coordinates between zero and t map "
                        + "to only p residues through u-xv. Two distinct pairs therefore "
                        + "collide. Their coordinate differences a and b satisfy a congruent "
                        + "to xb modulo p, and each absolute value is at most t.")),
                    Paragraph(Text(
                        "Both differences are nonzero. If b were zero, the collision and the "
                        + "bounds below p would force a to be zero, contradicting that the two "
                        + "pairs differ. If a were zero, the premise that p does not divide x "
                        + "allows cancellation of x modulo p and forces b to be zero as well. "
                        + "This also records why the premise cannot be dropped: when p divides "
                        + "x, every bounded a congruent to xb is zero.")),
                    Paragraph(Text(
                        "Library search used pinned Mathlib revision "
                        + "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Exact hits were "
                        + "Fintype.exists_ne_map_eq_of_card_lt for the collision, "
                        + "Nat.lt_succ_sqrt for the square cardinality, "
                        + "Int.natAbs_coe_sub_coe_le_of_le for the two bounds, and "
                        + "ZMod.intCast_eq_intCast_iff for the final congruence. Searches of "
                        + "the repository and pinned Mathlib found no declaration already "
                        + "combining these into Thue's two-nonzero-representative statement.")),
                    Paragraph(Text(
                        "The subsequent factorial application is kept as context rather than "
                        + "added to this theorem. There x is a factorial whose square is "
                        + "congruent to minus one modulo p, which in particular ensures that p "
                        + "does not divide x before this lemma is applied.")))
            ))));
}
