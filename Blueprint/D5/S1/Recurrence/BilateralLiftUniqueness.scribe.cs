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
                    LatexStatement.Create(
                        @"$$\operatorname{Sol}(F)=\langle e_{\varphi},e_{\psi}\rangle,\quad "
                        + @"Se_{\lambda}=\lambda e_{\lambda},\quad "
                        + @"F_{k+1}=\frac{\varphi^{k+1}-\psi^{k+1}}{\sqrt{5}},\quad "
                        + @"\langle F\rangle_S=\langle e_{\varphi},e_{\psi}\rangle.$$"),
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
                    LatexStatement.Create(
                        @"$$\operatorname{Sol}(u_{k+2}=u_{k+1}+u_k)="
                        + @"\operatorname{span}_{\mathbb{R}}\{e_{\varphi},e_{\psi}\}.$$"),
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
                    LatexStatement.Create(
                        @"$$Se_{\varphi}=\varphi e_{\varphi},\qquad "
                        + @"Se_{\psi}=\psi e_{\psi}.$$"),
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
                    LatexStatement.Create(
                        @"$$F_{k+1}=\frac{\varphi^{k+1}-\psi^{k+1}}{\sqrt{5}}.$$"),
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
                    LatexStatement.Create(
                        @"$$\langle F\rangle_{S}="
                        + @"\operatorname{span}_{\mathbb{R}}\{e_{\varphi},e_{\psi}\}.$$"),
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
                    LatexStatement.Create(
                        @"$$F_{k+2}-\varphi F_{k+1}=\psi^{k+1}.$$"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Subtracting the expanding golden component from the shifted Fibonacci "
                        + "weight leaves the contracting eigensequence exactly.")))
                ))));
}
