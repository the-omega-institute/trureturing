using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class RealRootedCoefficientNewtonDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef NewtonSource =
        LibraryNoteRef.Create("D5/L/Combinatorics/tao2026newton");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Newton inequalities for elementary symmetric functions of real multisets.",
        H("Newton inequalities from the upstream symmetric-function proof"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("elementary-symmetric-newton"),
                DeclarationHandle.Create("D5/S3/Analytic/RealRootedCoefficientNewton.esymm_mul_esymm_le_sq_esymm"),
                H("The reduced Newton inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(NewtonSource),
                Blocks(
                    Paragraph(Text("For a multiset s of N real numbers and every natural k, the product (k+2)(N-k)e_k e_(k+2) is at most (k+1)(N-k-1)e_(k+1)^2, where e_j is its j-th elementary symmetric function. No sign or distinctness assumption is imposed on the entries, and indices beyond N are included.")),
                    Paragraph(Text("The upstream proof represents elementary symmetric functions by a product of linear factors. The derivative has real roots with multiplicities; normalizing its leading coefficient reduces the number of entries while preserving normalized symmetric functions. Strong induction, the second-degree sum-of-squares inequality, and inversion at the last index prove Newton's inequality. In the Crown theorem, Vieta's formula for the negated root multiset converts this result to the needed coefficient inequalities. The license note identifies the immutable source and preserves its complete Apache license."))),
                DescribeRole.Theorem))));
}
