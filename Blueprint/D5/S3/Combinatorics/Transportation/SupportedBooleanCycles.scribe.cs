using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;
internal sealed class SupportedBooleanCyclesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tables are arbitrary Boolean functions on two independently universed finite labeled carriers. Supported means that each true cell lies in the allowed relation E. SameMargins equates every individually indexed row and column true-count. The distance is the number of cells at which the two tables disagree.", H("SupportedBooleanCycles"), Blocks(
        Describe.Lean(DescribeId.Create("correcting-step"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/SupportedBooleanCycles.correcting_step"),
            H("One supported conformal cycle flip"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Tables are arbitrary Boolean functions on two independently universed finite labeled carriers. Supported means that each true cell lies in the allowed relation E. SameMargins equates every individually indexed row and column true-count. The distance is the number of cells at which the two tables disagree."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("bounded-chain"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/SupportedBooleanCycles.bounded_conformal_chain"),
            H("A bounded finite chain to the target"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Tables are arbitrary Boolean functions on two independently universed finite labeled carriers. Supported means that each true cell lies in the allowed relation E. SameMargins equates every individually indexed row and column true-count. The distance is the number of cells at which the two tables disagree."))), DescribeRole.Theorem),
        Paragraph(Text("A Cycle has length k at least two and injective row and column maps from Fin k. The red matching pairs row i with column i; the blue matching pairs row i with the cyclic successor column. LegalStep allows either alternating polarity, requires both matchings inside E and opposite target bits, and sets the next table equal to the actual Boolean flip on their union. All external cells are fixed.")),
        Paragraph(Text("The two matchings are disjoint because their current bits are opposite. Their union therefore has exactly twice k distinct cells. Flipping corrects each selected disagreement. Each used row loses and gains one true cell, and the inverse cyclic permutation gives the same statement for every used column. The next table is supported and its distance plus twice k equals the old distance.")),
        Paragraph(Text("Chain is an inductive finite sequence with final node B. Its zero-step constructor starts and ends at B; its step constructor records the starting support, the complete individual margins and an actual LegalStep followed by the remaining chain. Strong induction on distance constructs a chain of n steps with n at most distance divided by four.")),
        Paragraph(Text("Every selected cell becomes equal to B and every correct cell is fixed, so a cell cannot change twice. Empty carriers and identical endpoints use the zero-step constructor. The allowed relation has no ordering, nesting, completeness, positivity, dimension or supplied decomposition assumption. This is a repository-derived Boolean update and chain construction using the retained simple-cycle supplier; no literature-priority assertion is made.")))));
}
