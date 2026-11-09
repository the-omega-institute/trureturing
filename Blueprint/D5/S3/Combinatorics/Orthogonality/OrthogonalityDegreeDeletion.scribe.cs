using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;

internal sealed class OrthogonalityDegreeDeletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Orthogonality/OrthogonalityDegreeDeletion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026deletion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact degrees and reversible deletion in the complete nonzero binary subspace graph.",
        H("Subspace degrees and extension of every retained coloring"),
        Blocks(
            Describe.Lean(DescribeId.Create("contained-subspace-cardinality"),
                DeclarationHandle.Create(Prefix + "below_card"), H("Every contained nonzero subspace"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The original proved subtype map/comap count is exposed for the live six-dimensional "
                    + "label-list consumer. Every nonzero submodule contained in X is counted by "
                    + "N(finrank X); its existing proof body is reused without a second lattice count."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-neighbor-cardinality"),
                DeclarationHandle.Create(Prefix + "degree_card"), H("Exact degrees"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every natural n and every actual nonzero submodule U of Fin n -> ZMod 2, "
                        + "write d=finrank U and N(r)=NikandishClique.nonzeroSubspaceCount r. "
                        + "The cardinality of U's neighbor set is N(n-d)-1 if U is contained in its "
                        + "orthogonal, and N(n-d) otherwise. The condition is pairwise total "
                        + "isotropy, not merely the existence of a self-isotropic vector.")),
                    Paragraph(Text(
                        "Nonzero submodules contained in U-perp correspond bijectively to nonzero "
                        + "submodules of U-perp itself, by subtype map and comap. A basis identifies "
                        + "that space with the binary coordinate space of dimension n-d. Finally "
                        + "erase U itself exactly when it is in this lattice. The graph is loopless. "
                        + "No catalogue completeness, Gaussian-binomial formula or finite computation "
                        + "is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reversible-safe-deletion"),
                DeclarationHandle.Create(Prefix + "result"), H("Preserve every retained color"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary n,k and a finite set D of actual nonzero submodules, assume "
                        + "N(n-dim U)<k for each U in D. Every Fin k coloring of the induced graph "
                        + "outside D extends to the complete orthogonality graph, with exactly the "
                        + "same color at each vertex outside D. Thus restriction and extension give "
                        + "equivalent k-colorability, and a fixed clique disjoint from D keeps "
                        + "all its assigned colors.")),
                    Paragraph(Text(
                        "Induct on the deleted set. Restore one vertex using a color outside the "
                        + "image of its already colored neighbors. That image has cardinality at "
                        + "most the vertex degree, which is strictly less than k by the exact formula. "
                        + "For a fixed k-clique, f adjacent fixed vertices use f distinct colors; "
                        + "both the residual degree bound and palette size lose these f colors. "
                        + "The inequality N(n-d)<k is therefore sufficient for the source's list "
                        + "deletion rule. The extension theorem preserves all retained colors, "
                        + "including these fixed assignments.")),
                    Paragraph(Text(
                        "The quantifiers include empty D, dimension zero and an empty palette. "
                        + "If a nonempty D satisfies the strict inequality then k is positive. "
                        + "No n=7 coloring or solver certificate is claimed. Historical k=16 "
                        + "preprocessing counts and later obstructions remain source reports. "
                        + "The exact n=7 chromatic number and the paused 19-color exclusion work "
                        + "remain open and untouched."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/Orthogonality/NikandishClique"))]));
}
