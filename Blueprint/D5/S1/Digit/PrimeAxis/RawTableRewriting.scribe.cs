using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.PrimeAxis;

internal sealed class RawTableRewritingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw Table Rewriting.",
        H("Raw Table Rewriting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rawtablerewriting-table-rewriting-terminates"),
                DeclarationHandle.Create("D5/S1/Digit/PrimeAxis/RawTableRewriting.table_rewriting_terminates"),
                H("Every directed table execution terminates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A raw table assigns natural multiplicities to finitely many prime-index pairs. "
                    + "Its Fibonacci value bounds the number of tokens; value zero means the empty "
                    + "table, from which no carry is possible. For positive initial value V, let J "
                    + "be the largest index whose Fibonacci weight is at most V. Every reachable "
                    + "token has index at most J, and its square-index sum S is at most V times J squared. "
                    + "Each directed carry strictly decreases the lexicographic triple consisting "
                    + "of token count C, index sum I, and V times J squared minus S. Adjacent and "
                    + "index-zero carries decrease C by one; repeated carries above index one "
                    + "preserve C and decrease I by one; the index-one carry preserves C and I "
                    + "and increases S by two. The lexicographic order is well founded, as is "
                    + "the reverse of table reduction, so no infinite execution exists. Every "
                    + "maximal execution is finite and ends at an irreducible table. Irreducibility "
                    + "is equivalent to each row being canonical: every multiplicity is at most "
                    + "one and adjacent ones are absent. Any irreducible table reached from a "
                    + "given start equals its rowwise normal form and is the unique such endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rawtablerewriting-finite-legal-words"),
                DeclarationHandle.Create("D5/S1/Digit/PrimeAxis/RawTableRewriting.finite_legal_words"),
                H("Only finitely many legal carry words start at a table"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any raw table, only finitely many tables have the same value in every "
                    + "prime row, and only finitely many labelled rules are enabled. Strong "
                    + "termination and finite branching imply that the set of all legal rule "
                    + "words starting at that table is finite, including the empty word. "
                    + "A letter records its selected prime and one of the four directed carries. "
                    + "An enabled letter gives exactly an actual table step, with the same prime "
                    + "and signed charge; conversely, every actual step arises from such a letter. "
                    + "Legality requires precisely the left-side multiplicities and preserves "
                    + "every other prime row. Different ordered lists of letters remain different words."))),
                DescribeRole.Theorem))));
}
