using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciRecurrencePolynomialRootsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complex root multiset of every odd-index plus-recurrence polynomial is given by a simple cosine formula.",
        H("Exact Complex Roots of the Odd Recurrence Polynomial"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-recurrence-polynomial-roots"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciRecurrencePolynomialRoots.odd_recurrence_polynomial_root_multiset"),
                H("Odd recurrence root multiset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural r, after mapping the integer recurrence polynomial at index 2r+1 into the complex polynomial ring, "
                    + "its root multiset is the list indexed by 0 <= k < 2r whose kth entry is "
                    + "-2 times the imaginary unit times cos((k+1) pi/(2r+1)). "
                    + "The indexing records each root with its multiplicity."))),
                DescribeRole.Theorem))));
}
