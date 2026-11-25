using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class CubicProbeFourierBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Split and nonsplit restrictions have unequal normalized Fourier costs for the same exact period-forcing target.",
        H("Cubic Probe Fourier Budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubic-fourier-budget-iff"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/CubicProbeFourierBudget.cubic_fourier_budget_iff"),
                H("Sharp cubic Fourier budget for finite-horizon period forcing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a positive horizon P, prescribe split and nonsplit observations at disjoint sites from zero through P. The prescription forces every compatible binary signal to have no positive period at most P. Such a prescription with the explicit normalized cubic coefficient tensor's absolute mass at most M exists exactly when there are counts a and b with a times b at least P minus floor(P/2) and 3 to the a times 2 to the b at most M.")),
                    Paragraph(Text("The unweighted nonsimply-bordered partial-word geometry is due to Blanchet-Sadri, Allen, Byrum and Mercas (LATA 2009, Theorem 1, DOI 10.1007/978-3-642-00982-2_15). Here the two weights come from the actual cyclic cubic identity filter and its complement, rather than assigning one cost to either mark.")),
                    Paragraph(Text("The result is a rational coefficient-table and combinatorial design theorem for independent cubic labels. It does not assert Galois independence, a GRH explicit formula or prime bound, or the WSS factorization conjecture."))),
                DescribeRole.Theorem))));
}
