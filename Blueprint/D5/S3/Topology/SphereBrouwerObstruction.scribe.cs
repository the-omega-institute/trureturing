using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class SphereBrouwerObstructionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/feldmanwilce2026spherecovers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Euclidean sphere cannot be contracted.",
        H("The Euclidean sphere cannot be contracted"),
        Blocks(Describe.Lean(
            DescribeId.Create("sphere-brouwer-obstruction"),
            DeclarationHandle.Create("D5/S3/Topology/SphereBrouwerObstruction.not_contractible_unit_sphere"),
            H("Noncontractibility from reduced singular homology"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For every positive natural n, the unit sphere of real Euclidean n-space is not contractible. Ambient dimension one is included.")),
                Paragraph(Text("TauCeti computes the sphere's reduced singular homology with integer coefficients in degree n-1 and identifies it with the nonzero integer coefficient module. The upstream proof transports this computation from a Euclidean space of the same dimension, so its statement applies to every nontrivial finite-dimensional real normed space.")),
                Paragraph(Text("A contraction would make reduced singular homology zero in every degree. The sphere computation would then force the integer coefficient module to be zero, contradicting the fact that zero and one are distinct.")),
                Paragraph(Text("The endpoint is adopted from the exact TauCeti.not_contractibleSpace_sphere declaration by a source port, because the supplier and receiving Mathlib pins differ. The immutable source revision and path, TauCeti copyright, complete Apache-2.0 license, modification notices and own-pinned-Mathlib retirement condition are recorded in the linked Library note and port sources. The homology obstruction and lower-six result carry no novelty claim."))),
            DescribeRole.Theorem))));
}
