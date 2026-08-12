using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class BilateralLiftUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create("Fibonacci solutions split into two golden eigenlines with a minimal cyclic carrier.",
H("Bilateral Fibonacci Lift Uniqueness"),
Blocks(
                Describe.Lean(
                    DescribeId.Create("bilateral-lift-uniqueness"),
                    DeclarationHandle.Create("D5/S1/Recurrence/BilateralLiftUniqueness.bilateral_lift_uniqueness"),
                    H("Bilateral lift uniqueness"),
                    StatementSource.FromAuthor(Disp(Seq(Operatorname, Grp(F.Id("Sol")), Open, F.Id("F"), Close, Eq, Langle, Sp, F.Id("e"), Underscore, Grp(Varphi), Comma, F.Id("e"), Underscore, Grp(Psi), Rangle, Comma, Quad, Sp, F.Id("Se"), Underscore, Grp(LambdaLower), Eq, LambdaLower, Sp, F.Id("e"), Underscore, Grp(LambdaLower), Comma, Quad, Sp, F.Id("F"), Underscore, Grp(F.Id("k"), Plus, D(1)), Eq, Frac, Grp(Varphi, Caret, Grp(F.Id("k"), Plus, D(1)), Minus, Psi, Caret, Grp(F.Id("k"), Plus, D(1))), Grp(Sqrt, Grp(D(5))), Comma, Quad, Sp, Langle, Sp, F.Id("F"), Rangle, Underscore, F.Id("S"), Eq, Langle, Sp, F.Id("e"), Underscore, Grp(Varphi), Comma, F.Id("e"), Underscore, Grp(Psi), Rangle, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The aggregate theorem packages the two-dimensional recurrence space, "
                        + "both shift eigenlines, Binet decomposition, cyclic minimality, and "
                        + "the exact contracting residual into one kernel-checked statement."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("two-dimensional-golden-solution-space"),
                    DeclarationHandle.Create("D5/S1/Recurrence/BilateralLiftUniqueness."
                        + "fibonacci_solution_space_eq_span"),
                    H("Golden decomposition of the solution space"),
                    StatementSource.FromAuthor(Disp(Seq(Operatorname, Grp(F.Id("Sol")), Open, F.Id("u"), Underscore, Grp(F.Id("k"), Plus, D(2)), Eq, F.Id("u"), Underscore, Grp(F.Id("k"), Plus, D(1)), Plus, F.Id("u"), Underscore, F.Id("k"), Close, Eq, Operatorname, Grp(F.Id("span")), Underscore, Grp(Mathbb, Grp(F.Id("R"))), OpenBrace, F.Id("e"), Underscore, Grp(Varphi), Comma, F.Id("e"), Underscore, Grp(Psi), CloseBrace, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The real solution space of the Fibonacci recurrence is exactly the "
                        + "span of the expanding and contracting golden eigensequences."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("shift-eigenlines"),
                    DeclarationHandle.Create("D5/S1/Recurrence/BilateralLiftUniqueness.shift_golden_eigenvectors"),
                    H("Shift eigenlines"),
                    StatementSource.FromAuthor(Disp(Seq(F.Id("Se"), Underscore, Grp(Varphi), Eq, Varphi, Sp, F.Id("e"), Underscore, Grp(Varphi), Comma, Qquad, Sp, F.Id("Se"), Underscore, Grp(Psi), Eq, Psi, Sp, F.Id("e"), Underscore, Grp(Psi), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Forward shift acts by the expanding golden ratio on one line and by "
                        + "its algebraic conjugate on the other."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("shifted-binet-formula"),
                    DeclarationHandle.Create("D5/S1/Recurrence/BilateralLiftUniqueness.fibonacci_weight_binet"),
                    H("Shifted Binet formula"),
                    StatementSource.FromAuthor(Disp(Seq(F.Id("F"), Underscore, Grp(F.Id("k"), Plus, D(1)), Eq, Frac, Grp(Varphi, Caret, Grp(F.Id("k"), Plus, D(1)), Minus, Psi, Caret, Grp(F.Id("k"), Plus, D(1))), Grp(Sqrt, Grp(D(5))), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "With Fibonacci weights indexed from F_1, both golden components have "
                        + "nonzero coefficient and their difference is normalized by sqrt(5)."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("minimal-shift-invariant-carrier"),
                    DeclarationHandle.Create("D5/S1/Recurrence/BilateralLiftUniqueness."
                        + "fibonacci_cyclic_span_minimal"),
                    H("Minimal shift-invariant carrier"),
                    StatementSource.FromAuthor(Disp(Seq(Langle, Sp, F.Id("F"), Rangle, Underscore, Grp(F.Id("S")), Eq, Operatorname, Grp(F.Id("span")), Underscore, Grp(Mathbb, Grp(F.Id("R"))), OpenBrace, F.Id("e"), Underscore, Grp(Varphi), Comma, F.Id("e"), Underscore, Grp(Psi), CloseBrace, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The golden two-line span contains the Fibonacci weight sequence, is "
                        + "shift-invariant, and lies in every shift-invariant real submodule "
                        + "that contains that sequence. This is the formal uniqueness carrier."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("contracting-residual"),
                    DeclarationHandle.Create("D5/S1/Recurrence/BilateralLiftUniqueness.fibonacci_weight_residual"),
                    H("Exact contracting residual"),
                    StatementSource.FromAuthor(Disp(Seq(F.Id("F"), Underscore, Grp(F.Id("k"), Plus, D(2)), Minus, Varphi, Sp, F.Id("F"), Underscore, Grp(F.Id("k"), Plus, D(1)), Eq, Psi, Caret, Grp(F.Id("k"), Plus, D(1)), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Subtracting the expanding golden component from the shifted Fibonacci "
                        + "weight leaves the contracting eigensequence exactly."))),
                    DescribeRole.Theorem))));
}
