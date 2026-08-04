using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BilateralLiftUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Recurrence/BilateralLiftUniqueness",
                "Fibonacci solutions split into two golden eigenlines with a minimal cyclic carrier."),
            H("Bilateral Fibonacci Lift Uniqueness"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("bilateral-lift-uniqueness"),
                    H("Bilateral lift uniqueness"),
                    LeanTheorem(
                        "D5/S1/Recurrence/BilateralLiftUniqueness.bilateral_lift_uniqueness"),
                    Disp(Seq(Operatorname, Grp(F.Id("Sol")), Open, F.Id("F"), Close, Eq, Langle, Sp, F.Id("e"), Underscore, Grp(Varphi), Comma, F.Id("e"), Underscore, Grp(Psi), Rangle, Comma, Quad, Sp, F.Id("Se"), Underscore, Grp(LambdaLower), Eq, LambdaLower, Sp, F.Id("e"), Underscore, Grp(LambdaLower), Comma, Quad, Sp, F.Id("F"), Underscore, Grp(F.Id("k"), Plus, D(1)), Eq, Frac, Grp(Varphi, Caret, Grp(F.Id("k"), Plus, D(1)), Minus, Psi, Caret, Grp(F.Id("k"), Plus, D(1))), Grp(Sqrt, Grp(D(5))), Comma, Quad, Sp, Langle, Sp, F.Id("F"), Rangle, Underscore, F.Id("S"), Eq, Langle, Sp, F.Id("e"), Underscore, Grp(Varphi), Comma, F.Id("e"), Underscore, Grp(Psi), Rangle, Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The aggregate theorem packages the two-dimensional recurrence space, "
                        + "both shift eigenlines, Binet decomposition, cyclic minimality, and "
                        + "the exact contracting residual into one kernel-checked statement.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("two-dimensional-golden-solution-space"),
                    H("Golden decomposition of the solution space"),
                    LeanTheorem(
                        "D5/S1/Recurrence/BilateralLiftUniqueness."
                        + "fibonacci_solution_space_eq_span"),
                    Disp(Seq(Operatorname, Grp(F.Id("Sol")), Open, F.Id("u"), Underscore, Grp(F.Id("k"), Plus, D(2)), Eq, F.Id("u"), Underscore, Grp(F.Id("k"), Plus, D(1)), Plus, F.Id("u"), Underscore, F.Id("k"), Close, Eq, Operatorname, Grp(F.Id("span")), Underscore, Grp(Mathbb, Grp(F.Id("R"))), OpenBrace, F.Id("e"), Underscore, Grp(Varphi), Comma, F.Id("e"), Underscore, Grp(Psi), CloseBrace, Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The real solution space of the Fibonacci recurrence is exactly the "
                        + "span of the expanding and contracting golden eigensequences.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("shift-eigenlines"),
                    H("Shift eigenlines"),
                    LeanTheorem(
                        "D5/S1/Recurrence/BilateralLiftUniqueness.shift_golden_eigenvectors"),
                    Disp(Seq(F.Id("Se"), Underscore, Grp(Varphi), Eq, Varphi, Sp, F.Id("e"), Underscore, Grp(Varphi), Comma, Qquad, Sp, F.Id("Se"), Underscore, Grp(Psi), Eq, Psi, Sp, F.Id("e"), Underscore, Grp(Psi), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Forward shift acts by the expanding golden ratio on one line and by "
                        + "its algebraic conjugate on the other.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("shifted-binet-formula"),
                    H("Shifted Binet formula"),
                    LeanTheorem(
                        "D5/S1/Recurrence/BilateralLiftUniqueness.fibonacci_weight_binet"),
                    Disp(Seq(F.Id("F"), Underscore, Grp(F.Id("k"), Plus, D(1)), Eq, Frac, Grp(Varphi, Caret, Grp(F.Id("k"), Plus, D(1)), Minus, Psi, Caret, Grp(F.Id("k"), Plus, D(1))), Grp(Sqrt, Grp(D(5))), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "With Fibonacci weights indexed from F_1, both golden components have "
                        + "nonzero coefficient and their difference is normalized by sqrt(5).")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("minimal-shift-invariant-carrier"),
                    H("Minimal shift-invariant carrier"),
                    LeanTheorem(
                        "D5/S1/Recurrence/BilateralLiftUniqueness."
                        + "fibonacci_cyclic_span_minimal"),
                    Disp(Seq(Langle, Sp, F.Id("F"), Rangle, Underscore, Grp(F.Id("S")), Eq, Operatorname, Grp(F.Id("span")), Underscore, Grp(Mathbb, Grp(F.Id("R"))), OpenBrace, F.Id("e"), Underscore, Grp(Varphi), Comma, F.Id("e"), Underscore, Grp(Psi), CloseBrace, Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The golden two-line span contains the Fibonacci weight sequence, is "
                        + "shift-invariant, and lies in every shift-invariant real submodule "
                        + "that contains that sequence. This is the formal uniqueness carrier.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("contracting-residual"),
                    H("Exact contracting residual"),
                    LeanTheorem(
                        "D5/S1/Recurrence/BilateralLiftUniqueness.fibonacci_weight_residual"),
                    Disp(Seq(F.Id("F"), Underscore, Grp(F.Id("k"), Plus, D(2)), Minus, Varphi, Sp, F.Id("F"), Underscore, Grp(F.Id("k"), Plus, D(1)), Eq, Psi, Caret, Grp(F.Id("k"), Plus, D(1)), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Subtracting the expanding golden component from the shifted Fibonacci "
                        + "weight leaves the contracting eigensequence exactly.")))
                ))));
}
