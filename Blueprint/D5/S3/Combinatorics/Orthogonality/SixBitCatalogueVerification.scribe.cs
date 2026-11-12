using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class SixBitCatalogueVerificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact six-dimensional source representation and certificate.",
        H("Complete source objects and retained trust boundaries"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-completeness-check"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.catalogue_covers"),
                H("Kernel completeness check"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The complete adjoining-vector predicate and original table are unchanged. The source proved this obligation using native_decide; current admission uses kernel reduction and requires a successful current build and transitive-axiom report. Historical native-evaluation provenance remains explicit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-properness-check"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.catalogue_proper"),
                H("Kernel properness check"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The exact source obligation checks all relevant catalogue masks, colors and perpendicular relations. Current kernel reduction replaces the historical native_decide proof without changing the predicate or input."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-clique-validity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.clique_valid"),
                H("Kernel clique validity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("Kernel reduction checks that each of the fifteen specified spaces is a nonzero XOR-closed space. The original native_decide provenance remains historical evidence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-clique-adjacency"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.clique_adjacent"),
                H("Kernel clique adjacency"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("Kernel reduction checks every distinct specified clique pair for adjacency, with the original predicate and clique indices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-source-chromatic-number"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.chromatic_number_six"),
                H("full source chromatic number"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The complete positive certificate and the fifteen-clique give chromatic number fifteen for the all-space graph. The historical source proof had four native-evaluation axioms. The current candidate requests kernel reduction for those exact obligations; its accepted axiom closure and normal admission require current successful evidence. This theorem does not supply the separate line-graph result twelve."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-full-submodule-chromatic-number"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.actual_chromatic_number_six"),
                H("Every actual nonzero Submodule"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                    "D5/L/QuadraticForms/binarysubspace2026complete")),
                Blocks(Paragraph(Text("The complete proved graph isomorphism transfers the source certificate to the graph on every actual nonzero Submodule of Fin6->ZMod2, including the whole space. Both the fifteen-color upper bound and the actual fifteen-clique are consumed. This target theorem remains pending until the exact original certificate obligations compile without extra axioms and the current normal checks succeed."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge"))]));
}
