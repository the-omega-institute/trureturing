using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class HalfFactorialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half of the nonzero residues gives an explicit square root criterion for minus one.",
        H("The Half-Factorial Criterion for Minus One"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("half-factorial-criterion-with-explicit-witness"),
                DeclarationHandle.Create("D5/S3/ArithUnits/HalfFactorial.half_factorial_mod_prime"),
                H("The signed half-factorial square, its witness, and its obstruction"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Forall, Sp, F.Id("p"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Quad, Sp,
                                    F.Id("p"), Esc, F.Text, Grp(F.Id("prime")), Comma, Quad, Sp,
                                    F.Id("m"), Eq, Frac, Grp(F.Id("p"), Minus, D(1)), Grp(D(2)), Colon, Quad,
                                    Open, F.Id("p"), Minus, D(1), Close, Bang, Equiv,
                                    Open, Minus, D(1), Close, Caret, Grp(F.Id("m")),
                                    Open, F.Id("m"), Bang, Close, Caret, Grp(D(2)),
                                    Esc, Open, Operatorname, Grp(F.Id("mod")), Esc, F.Id("p"), Close,
                                    Sp, Land, Sp,
                                    Open, F.Id("p"), Equiv, D(1), Esc, Open, Operatorname, Grp(F.Id("mod")),
                                    Sp, D(4), Close, Sp, Rightarrow, Sp,
                                    Open, F.Id("m"), Bang, Close, Caret, Grp(D(2)), Equiv, Minus, D(1),
                                    Esc, Open, Operatorname, Grp(F.Id("mod")), Esc, F.Id("p"), Close, Close,
                                    Sp, Land, Sp,
                                    Open, F.Id("p"), Equiv, D(3), Esc, Open, Operatorname, Grp(F.Id("mod")),
                                    Sp, D(4), Close, Sp, Rightarrow, Sp, Neg, Exists, Sp,
                                    F.Id("x"), InMacro, Mathbb, Grp(F.Id("Z")), Slash, F.Id("p"),
                                    Mathbb, Grp(F.Id("Z")), Comma, Quad, Sp,
                                    F.Id("x"), Caret, Grp(D(2)), Eq, Minus, D(1), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "For every natural prime p, set m = (p - 1) / 2. The factorial "
                                        + "(p - 1)! is congruent to (-1)^m times (m!)^2 modulo p. When p is "
                                        + "one modulo four, the specific residue represented by m! squares to "
                                        + "minus one; this is an explicit witness, not merely an existence "
                                        + "claim. When p is three modulo four, every residue fails to square to "
                                        + "minus one.")),
                                    Paragraph(Text(
                                        "The prime p = 2 remains inside the first clause: then m = 0 and both "
                                        + "sides equal one in ZMod 2. It triggers neither conditional corollary, "
                                        + "because two is neither one nor three modulo four.")),
                                    Paragraph(Text(
                                        "Library search used pinned Mathlib revision "
                                        + "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Exact hits were "
                                        + "Nat.factorial_mul_descFactorial and ZMod.cast_descFactorial for the "
                                        + "factorial split, repository theorem Wilson.wilson_theorem for Wilson's "
                                        + "congruence, and ZMod.mod_four_ne_three_of_sq_eq_neg_one for the "
                                        + "nonexistence direction. Searches for a theorem already combining "
                                        + "factorial, (p - 1) / 2, and the signed square found no matching "
                                        + "declaration, so the Lean proof only assembles these existing results."))),
                DescribeRole.Theorem
            ))));
}
