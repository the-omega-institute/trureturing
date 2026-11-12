using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class TotalCodeParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite total perfect code induces a matching and has even cardinality.",
        H("Open-neighbor parity"),
        Blocks(Describe.Lean(DescribeId.Create("induced-matching-parity"),
            DeclarationHandle.Create("D5/S3/Combinatorics/CayleySumCodes/TotalCodeParity.result"),
            H("Degree one on the code"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/GraphInvariants/Nikandish/manikandishzhang2026sumcodes")),
            Blocks(Paragraph(Text(
                "In any simple graph on a finite group, a total perfect code C has exactly "
                + "one neighbor at every vertex of the induced graph on C. Its components "
                + "are therefore edges, and its cardinality is even. The proof transfers "
                + "the actual unique-neighbor predicate to the induced graph and applies "
                + "Mathlib's handshaking lemma. It includes arbitrary code subsets and hence "
                + "the subgroup codes of the manuscripts. Self-neighbors never count. "
                + "Even cardinality alone gives no converse existence theorem."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion"))]));
}
