using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CloitreActualGlobalConvergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/CloitreActualGlobalConvergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden convergence of the actual Cloitre sequence is equivalent to vanishing positive selected jumps.",
        H("Actual Cloitre Global Convergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cloitre-global-position"),
                DeclarationHandle.Create(Prefix + "position"),
                H("Half-open Fibonacci block position"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let q(n) be the greatest Fibonacci index with F(q(n)) at most n. "
                    + "The position of n is (n-F(q(n)))/F(q(n)-1). For n at least "
                    + "eight this position lies in the unit interval. It is an "
                    + "analysis coordinate, independent of the actual iteration time."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cloitre-global-convergence"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Positive jumps and the global golden limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural-valued upper envelope U satisfying the complete "
                        + "Hyp21_1, set alpha to the inverse golden ratio. Let beta be the "
                        + "limsup of C(N)/N over all natural roots, and kappa the limsup "
                        + "of max(g(N)-T(N,g(N)),0)/N, taking the signed difference "
                        + "before its positive part. Then beta is at most alpha plus "
                        + "the golden ratio times kappa. Moreover C(N)/N tends to alpha "
                        + "if and only if the positive selected-jump ratio tends to zero.")),
                    Paragraph(Text(
                        "For the upper bound, choose the least block-position cluster "
                        + "among roots approaching the global limsup. The actual split "
                        + "recurrence and uniformly positive child weights force both "
                        + "child ratios to approach the same extremum. If the upper "
                        + "bound failed, the selected child's weight would be strictly "
                        + "below alpha, placing it in the preceding Fibonacci block "
                        + "and giving a smaller extremal position.")),
                    Paragraph(Text(
                        "If the global value ratio converges, every point of the actual "
                        + "selected cycle has uniformly small value-ratio error. The "
                        + "inner map contracts normalized distance to alpha up to that "
                        + "error. Maximizing on the same finite cycle bounds the "
                        + "selector and its successor uniformly, so their positive "
                        + "jump vanishes. In the opposite direction the limsup bound "
                        + "and the golden floor lower envelope squeeze the value ratio "
                        + "to alpha. All finite source foundations remain conditional."))),
                DescribeRole.Theorem))));
}
