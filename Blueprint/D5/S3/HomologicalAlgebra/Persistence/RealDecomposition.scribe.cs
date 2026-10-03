using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Persistence;

internal sealed class RealDecompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/HomologicalAlgebra/Persistence/RealDecomposition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/bauer2015persistence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classify real interval sums, estimate image matching and construct actual interleavings.",
        H("Actual Natural Real Classification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-unique-decomposition"),
                DeclarationHandle.Create(Prefix + "exists_unique_decomposition"),
                H("Existence and uniqueness against arbitrary finite competitors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For every arbitrary field, finite-dimensional finite diagram and strictly "
                            + "increasing real grid, choose the already constructed homogeneous "
                            + "interval basis. Birth is its birth breakpoint; death is the next "
                            + "breakpoint after its last vertex or infinity for a final survivor.")),
                    Paragraph(Text(
                        "Supported coordinate restriction, Basis.equivFun and its reconstruction "
                            + "sum give component isomorphisms. The existing occurrence naturality "
                            + "equations give all real arrow squares, including the zero prefix "
                            + "and unrestricted final tail. An empty or zero chain has an empty "
                            + "occurrence set. These coordinate suppliers are applied inside "
                            + "the natural classification proof.")),
                    Paragraph(Text(
                        "Every competing finite positive-length interval family, with arbitrary "
                            + "real births and finite or infinite deaths, that is naturally isomorphic "
                            + "to the same actual module has the same endpoint occurrence counts. "
                            + "Component isomorphisms and naturality transport actual image ranks "
                            + "using the pinned range and finrank suppliers. The proof constructs "
                            + "the surviving-coordinate image equivalence, then uses common finite "
                            + "endpoint cuts and integer differences to isolate each multiplicity. "
                            + "Exact interleaving iff "
                            + "matching and extended isometry remain separate obligations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-quantitative-image-matching"),
                DeclarationHandle.Create(Prefix + "exists_quantitative_image_matching"),
                H("Fixed same-image matching with quantitative coverage"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The sorted union of both families' births and finite deaths determines "
                        + "a common grid. Endpoint membership establishes invertible source, "
                        + "target and image transports inside each cell. The zero prefix follows "
                        + "from actual target support, including an empty grid. Compatible "
                        + "sampled-image maps, using the image functor on invertible squares, "
                        + "form a natural isomorphism to the same categorical "
                        + "image; finite-diagram classification constructs one image family. "
                        + "Both transported factors use that family and compose to the original "
                        + "morphism. A finite reindexing preserves arbitrary occurrence universes. "
                        + "Sorted birth and death fibers and both ordinal-preserving embeddings "
                        + "are returned once, before the universal quantifier over the independent "
                        + "nonnegative kernel and cokernel parameters. Actual kernel and range "
                        + "conditions for the original morphism transfer to these same factors. "
                        + "Their trim estimates give target birth at most image birth, equal "
                        + "image and source births, and image birth at most target birth plus "
                        + "the cokernel parameter. Image and target deaths agree and are at "
                        + "most source death; finite source death is at most image death plus "
                        + "the kernel parameter. The fixed embeddings cover every source or "
                        + "target interval longer than its corresponding parameter and every "
                        + "essential. Source essential death is equivalent to image essential "
                        + "death on paired occurrences. Every unmatched finite interval has "
                        + "length at most its parameter. A zero kernel parameter forces full "
                        + "source coverage and equal deaths; a zero cokernel parameter forces "
                        + "full target coverage and equal births. Empty and zero families are "
                        + "allowed. Exact stability, natural converse interleavings and equality "
                        + "of extended-distance feasible sets remain separate conclusions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matching-interleaving"),
                DeclarationHandle.Create(Prefix + "matching_interleaving"),
                H("Actual interleaving from a partial occurrence matching"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Two occurrence embeddings specify the matched pairs without identifying "
                        + "repeated intervals. Both birth inequalities and both extended death "
                        + "inequalities have the same nonnegative radius. Every unmatched death "
                        + "is at most its birth plus twice that radius. Each forward component "
                        + "copies a matched source coordinate when the shifted target survives, "
                        + "and is zero otherwise; the reverse component is constructed symmetrically. "
                        + "The birth inequalities ensure supported values, and the death inequalities "
                        + "give every naturality square. A coordinate surviving the double shift "
                        + "necessarily survives the intermediate matched interval. Both composites "
                        + "therefore equal the actual double-shift structure maps. Unmatched "
                        + "coordinates vanish by their length bounds. No overlap, nonempty family "
                        + "or nonzero radius is assumed; essential deaths remain infinite. "
                        + "This is the supported-sum converse, not the full classification-based "
                        + "equivalence or extended-distance equality."))),
                DescribeRole.Theorem))));
}
