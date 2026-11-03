using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class CompactRangePersistenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/CompactRangePersistence.";
    private static AssessedProvenance Provenance => AssessedProvenance.FromRepo(
        LibraryNoteRef.Create("D5/L/Topology/retractive2026reviewed"));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classical arbitrary-set retractive attachment supplier; original Efimov KPI 0.",
        H("CompactRangePersistence"), Blocks(
            Paragraph(Text("Statements below are projected from the compiled Lean declarations with their complete actual telescopes. The scientific source and independent ordinary review are identified in the cited Library note; neither source-level review nor this exposition substitutes for kernel checking.")),
            Describe.Lean(DescribeId.Create("mem-range-limit-map"), DeclarationHandle.Create(Owner + "mem_range_limit_map"), H("Compact actual ranges persist at arbitrary cofiltered limits"), StatementSource.FromLean(), Provenance, Blocks(Paragraph(Text("F and G are actual TopCat diagrams over any small cofiltered category, t is a natural transformation, and b is an actual coherent thread of G. Each F stage is compact Hausdorff and every G stage is Hausdorff. The fibres t(j) inverse {b(j)} are actual closed compact nonempty subspaces. Naturality supplies their restricted maps. The pinned Mathlib theorem TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system gives a coherent fibre thread; forgetting the fibre proofs is an actual F thread mapping to b. The reused theorem proves finite consistency through one cofiltered upper named stage. Restricted fibre maps are not assumed onto. No countable cofinality, fibre independence, product fibres, or section is assumed. The index category can be the opposite of any ordinal prefix. This statement is stronger than the ordinal continuous-system instance."))), DescribeRole.Theorem))));
}
