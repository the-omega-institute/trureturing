using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class BilateralLiftUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Scale/BilateralLiftUniqueness",
                "Fibonacci solutions split into two golden eigenlines with a minimal cyclic carrier."),
            H("Bilateral Fibonacci Lift Uniqueness"),
            Blocks(
                new DocumentBlock.Describe(
                    DescribeId.Create("bilateral-lift-uniqueness"),
                    DescribeKind.Theorem,
                    H("Bilateral lift uniqueness"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Scale/BilateralLiftUniqueness.bilateral_lift_uniqueness")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The aggregate theorem packages the two-dimensional recurrence space, "
                        + "both shift eigenlines, Binet decomposition, cyclic minimality, and "
                        + "the exact contracting residual into one kernel-checked statement."))),
                    LatexStatement.Create(
                        @"$$\operatorname{Sol}(F)=\langle e_{\varphi},e_{\psi}\rangle,\quad "
                        + @"Se_{\lambda}=\lambda e_{\lambda},\quad "
                        + @"F_{k+1}=\frac{\varphi^{k+1}-\psi^{k+1}}{\sqrt{5}},\quad "
                        + @"\langle F\rangle_S=\langle e_{\varphi},e_{\psi}\rangle.$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("two-dimensional-golden-solution-space"),
                    DescribeKind.Theorem,
                    H("Golden decomposition of the solution space"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Scale/BilateralLiftUniqueness."
                        + "fibonacci_solution_space_eq_span")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The real solution space of the Fibonacci recurrence is exactly the "
                        + "span of the expanding and contracting golden eigensequences."))),
                    LatexStatement.Create(
                        @"$$\operatorname{Sol}(u_{k+2}=u_{k+1}+u_k)="
                        + @"\operatorname{span}_{\mathbb{R}}\{e_{\varphi},e_{\psi}\}.$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("shift-eigenlines"),
                    DescribeKind.Theorem,
                    H("Shift eigenlines"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Scale/BilateralLiftUniqueness.shift_golden_eigenvectors")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Forward shift acts by the expanding golden ratio on one line and by "
                        + "its algebraic conjugate on the other."))),
                    LatexStatement.Create(
                        @"$$Se_{\varphi}=\varphi e_{\varphi},\qquad "
                        + @"Se_{\psi}=\psi e_{\psi}.$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("shifted-binet-formula"),
                    DescribeKind.Theorem,
                    H("Shifted Binet formula"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Scale/BilateralLiftUniqueness.fibonacci_weight_binet")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "With Fibonacci weights indexed from F_1, both golden components have "
                        + "nonzero coefficient and their difference is normalized by sqrt(5)."))),
                    LatexStatement.Create(
                        @"$$F_{k+1}=\frac{\varphi^{k+1}-\psi^{k+1}}{\sqrt{5}}.$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("minimal-shift-invariant-carrier"),
                    DescribeKind.Theorem,
                    H("Minimal shift-invariant carrier"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Scale/BilateralLiftUniqueness."
                        + "fibonacci_cyclic_span_minimal")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The golden two-line span contains the Fibonacci weight sequence, is "
                        + "shift-invariant, and lies in every shift-invariant real submodule "
                        + "that contains that sequence. This is the formal uniqueness carrier."))),
                    LatexStatement.Create(
                        @"$$\langle F\rangle_{S}="
                        + @"\operatorname{span}_{\mathbb{R}}\{e_{\varphi},e_{\psi}\}.$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("contracting-residual"),
                    DescribeKind.Theorem,
                    H("Exact contracting residual"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Scale/BilateralLiftUniqueness.fibonacci_weight_residual")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Subtracting the expanding golden component from the shifted Fibonacci "
                        + "weight leaves the contracting eigensequence exactly."))),
                    LatexStatement.Create(
                        @"$$F_{k+2}-\varphi F_{k+1}=\psi^{k+1}.$$")))));
}
