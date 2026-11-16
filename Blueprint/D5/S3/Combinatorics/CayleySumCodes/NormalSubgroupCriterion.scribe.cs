using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class NormalSubgroupCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/NormalSubgroupCriterion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/FiniteGroups/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The corrected existential criterion for normal subgroup total perfect codes.",
        H("Perfect-code existence and the two possible internal square regimes"),
        Blocks(
            Paragraph(Text("For every finite group G, every subgroup H, every actual left transversal T of H and every g in G, the set of y in T with g inverse times y in H has cardinality one. Inversion converts the usual representative test y inverse times g in H to this test; uniqueness then gives the cardinality. No normality assumption on H is needed for this step, which also supplies the abelian regular total-code constructions.")),
            Describe.Lean(DescribeId.Create("normal-subgroup-total-code-criterion"),
            DeclarationHandle.Create(Prefix + "result"), H("The complete normal-H equivalence"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(
                "For every normal subgroup H of every finite group G, a total perfect "
                + "sum-graph witness exists exactly when a perfect-code witness exists and "
                + "either H contains a central nonsquare or its actual square set has "
                + "cardinality two. This is correction Corollary 2.4, replacing necessity "
                + "in the cited Zhang and Ahanjideh–Akhlaghi–Rodrigues normal-H total-code "
                + "parts while preserving the surviving singleton sufficiency. Normality "
                + "of H is an explicit hypothesis. The witnesses may depend on H and may "
                + "change between perfect and total perfect coding.")),
                Paragraph(Text(
                    "The forward route uses both fixed-connection-set branches. Their "
                    + "internal connection elements are central. In the two-element branch, "
                    + "if the square set has size one, its identity is the only square "
                    + "and the other internal connection element supplies a central "
                    + "nonsquare. Conversely a normalized identity-containing normal "
                    + "transversal supplies the outside cosets; replace its identity "
                    + "representative by the central nonsquare or by the two-element "
                    + "square set. Every count is over actual subgroup cosets and the "
                    + "full loopless graph. This is neither a regular-graph classification "
                    + "nor inheritance of code properties through arbitrary quotients."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/PerfectCodeTransversal")),
         DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/CodeCentralizers"))]));
}
