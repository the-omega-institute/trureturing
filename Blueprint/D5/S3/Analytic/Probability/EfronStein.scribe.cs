using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class EfronSteinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The variance of a bounded measurable observable on a finite dependent product is bounded by half its total coordinate resampling energy.",
        H("Efron–Stein inequality on finite probability products"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("efron-stein-pi"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/EfronStein.efronStein_pi"),
                H("Finite-product variance tensorization"),
                StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/armstrong2026efronstein")),
                Blocks(
                    Paragraph(Text("The index type is any finite type, including the empty type. Each coordinate has its own arbitrary measurable space and probability measure. The observable is a measurable real function on their dependent product with a single pointwise absolute bound M. The outer sample x follows the full product law, and the replacement y follows the probability measure of coordinate i. The coefficient is one half.")),
                    Paragraph(Text("Splitting off one coordinate gives the two-factor variance decomposition. The two-point variance identity supplies that coordinate’s resampling term; Jensen’s inequality bounds each resampling term of the conditional mean by the corresponding term of the original observable. Induction on the number of coordinates and a measure-preserving reindexing give the stated finite-product inequality. The empty product has zero variance and an empty energy sum.")),
                    Paragraph(Text("This is a credited port of Scott N. Armstrong’s CoarseGraining sources TwoPoint.lean, ProdDecomp.lean and Fin.lean at revision 310d1a6bab3ba2d398cdaffec32f3c9d4b5a24be. The original Apache-2.0 copyright and full license are retained, with source correspondence in the literature note. The source proof is consolidated and adapted to the receiving Mathlib API.")),
                    Paragraph(Text("Coordinates may differ and their measures need not be identical. No topology, Borel-space condition, symmetry or nondegeneracy is required. The conclusion concerns bounded observables and finite products; it supplies variance control from coordinate sensitivities."))),
                DescribeRole.Theorem))));
}
