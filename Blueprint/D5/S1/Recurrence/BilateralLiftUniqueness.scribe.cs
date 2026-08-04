using static StrataLint.Scribe.DefinitionDsl;

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
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Sol"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Langle), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi)]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Psi)]), new Formula.LatexMacro(FormulaLatexMacro.Rangle), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Quad), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("Se")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.LambdaLower)]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.LambdaLower), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.LambdaLower)]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Quad), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])]), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexMacro(FormulaLatexMacro.Psi), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])])]), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Sqrt), new Formula.LatexGroup([new Formula.LatexDigits([5])])]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Quad), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Langle), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexMacro(FormulaLatexMacro.Rangle), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("S")), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Langle), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi)]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Psi)]), new Formula.LatexMacro(FormulaLatexMacro.Rangle), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
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
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Sol"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([2])]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])]), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("u")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("span"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("R"))])]), new Formula.LatexMacro(FormulaLatexMacro.OpenBrace), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi)]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Psi)]), new Formula.LatexMacro(FormulaLatexMacro.CloseBrace), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
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
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("Se")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi)]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi)]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Qquad), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("Se")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Psi)]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Psi), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Psi)]), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
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
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])]), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexMacro(FormulaLatexMacro.Psi), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])])]), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Sqrt), new Formula.LatexGroup([new Formula.LatexDigits([5])])]), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
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
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Langle), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexMacro(FormulaLatexMacro.Rangle), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("S"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("span"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("R"))])]), new Formula.LatexMacro(FormulaLatexMacro.OpenBrace), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi)]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Psi)]), new Formula.LatexMacro(FormulaLatexMacro.CloseBrace), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
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
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([2])]), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Psi), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])]), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Subtracting the expanding golden component from the shifted Fibonacci "
                        + "weight leaves the contracting eigensequence exactly.")))
                ))));
}
