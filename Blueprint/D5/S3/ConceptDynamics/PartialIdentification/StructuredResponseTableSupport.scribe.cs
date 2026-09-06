using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class StructuredResponseTableSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/StructuredResponseTableSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quaternary coding gives an exact capacity count. A smaller structured generator is a genuine model restriction unless the omitted tables already have zero mass or are excluded by justified cross-stratum structure.",
        H("Exact support cost and structured table families"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supports-law"),
                DeclarationHandle.Create(Prefix + "SupportsLaw"),
                H("Cover every positive-mass table"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A deterministic latent-state generator is exact for a law only when every positive-mass atom is produced by some latent state."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("surjective-response-table-generator-requires-four-pow"),
                DeclarationHandle.Create(Prefix + "surjective_response_table_generator_requires_four_pow"),
                H("Universal table generation needs 4^k states"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Surjectivity onto all k-row Boolean response tables forces at least 4^k deterministic latent states by finite cardinality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("small-generator-not-universal"),
                DeclarationHandle.Create(Prefix + "small_generator_not_universal"),
                H("Every smaller family omits a table"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any latent family below the radix capacity fails to cover the unrestricted table carrier. This is a support statement, not a DFAO-state lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-response-table-full-support"),
                DeclarationHandle.Create(Prefix + "independentResponseTable_full_support"),
                H("Positive row kernels fill the full table space"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strict positivity of all four row-response masses makes every complete table have positive product mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-independent-table-law-generator-lower-bound"),
                DeclarationHandle.Create(Prefix + "positive_independent_table_law_generator_lower_bound"),
                H("Full-support probability laws inherit the capacity lower bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An exact deterministic latent generator of the positive independent-row law must cover every table and therefore needs at least 4^k states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-independent-table-law-not-supported-by-small-generator"),
                DeclarationHandle.Create(Prefix + "positive_independent_table_law_not_supported_by_small_generator"),
                H("Compression requires a restricted model family"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A smaller latent carrier cannot reproduce a full-support independent-row law exactly. Automata can still give short algorithmic descriptions of structured tables because that is a different complexity notion."))),
                DescribeRole.Theorem))));
}
