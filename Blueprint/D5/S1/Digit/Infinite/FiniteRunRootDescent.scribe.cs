using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class FiniteRunRootDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite high-run roots approach the complete cap root.",
        H("Finite high-run root descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finiterunrootdescent-root-rate-chain"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/FiniteRunRootDescent.root_rate_chain"),
                H("Strict descent of finite high-run roots"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every integer k at least two, the finite cap function has a unique root z in "
                    + "the interval (0,1). For every nonnegative high-run length n, the truncated cap "
                    + "function has a unique root zeta(n) in (0,1), and z is strictly below zeta(n). "
                    + "The roots form a strictly decreasing sequence converging to z. Applying the "
                    + "continuous logarithmic rate map -log(x)/log(2) makes the rates strictly increasing "
                    + "and convergent to the rate of z."))),
                DescribeRole.Theorem)),
            Describe.Lean(
                DescribeId.Create("finiterunrootdescent-root-rate-property"),
                DeclarationHandle.Create("D5/S1/Digit/Infinite/FiniteRunRootDescent.root_rate_property"),
                H("The root-rate property"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The root-rate property records the interval membership, root equations, uniqueness "
                    + "of the complete and truncated roots, strict ordering, convergence of the roots, "
                    + "and the corresponding monotonicity and convergence of their logarithmic rates."))),
                DescribeRole.Definition))
        ));
}
