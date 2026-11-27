using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class ZeroMassTriangleHeatDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/ZeroMassTriangleHeat.";
    private static readonly LibraryNoteRef Kron =
        LibraryNoteRef.Create("D5/L/GraphInvariants/dorflerbullo2013kron");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive triangles with a common massless Schur reduction have distinct collocated heat at the hidden-mass time scale.",
        H("Heat on a triangle with one vanishing mass"),
        Blocks(
            Paragraph(Text(
                "The triangle and heat expansion come from the heat calculation in "
                + "An exact zero-mass heat and control separation on a positive triangle "
                + "(triangle-exact-control.txt, 2026-11-24). Its vertices 1, 2 and 3 "
                + "are numbered 0, 1 and 2 here.")),
            Describe.Lean(
                DescribeId.Create("zero-mass-triangle-heat"),
                DeclarationHandle.Create(Prefix + "same_schur_distinct_heat_at_mass_time"),
                H("Common massless heat and distinct finite-mass heat"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Kron),
                Blocks(
                    Paragraph(Text(
                        "The two retained vertices have unit mass. The two edges to vertex 2 "
                        + "have conductance c, and the retained edge has conductance k − c/2. "
                        + "For each c strictly between zero and 2k, all three conductances "
                        + "are positive. With zero mass and no injection at vertex 2, "
                        + "its temperature is the average of the two retained temperatures. "
                        + "The eliminated diagonal is 2c and both couplings are −c, so "
                        + "Schur elimination subtracts c/2 from each entry of the retained block. "
                        + "This leaves a single edge of conductance k. "
                        + "The entire two-vertex heat operator is therefore independent of c "
                        + "at every time.")),
                    Paragraph(Text(
                        "For positive hidden mass ε, the finite-mass collocated heat is the "
                        + "temperature at vertex 0 per unit impulse at vertex 0. At time εs "
                        + "with s positive, the zero and antisymmetric mode terms cancel "
                        + "in the difference between any two c values. The positive symmetric "
                        + "mode has decay rate c(1+2/ε) and collocated weight ε/[2(2+ε)]. "
                        + "The remaining difference "
                        + "divided by ε is the difference of the exponentials with arguments "
                        + "−c₁(ε+2)s and −c₂(ε+2)s, divided by 2(2+ε). "
                        + "Injectivity of the exponential makes that difference nonzero for "
                        + "distinct conductances."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("triangle-heat-projectors"),
                DeclarationHandle.Create(Prefix + "spectral_projectors"),
                H("Orthogonal mode projections"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For ε positive, the zero, antisymmetric and symmetric modes give "
                    + "symmetric, pairwise orthogonal projections summing to the identity. "
                    + "The normalized stiffness acts on them with rates 0, 2k and c(1+2/ε)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("triangle-heat-coincidence"),
                DeclarationHandle.Create(Prefix + "coincident_positive_projector"),
                H("Projection at the repeated rate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When the two rates agree at positive ε, the sum of their mode projections "
                    + "is symmetric and idempotent. The normalized stiffness equals 2k times "
                    + "this projection. For the positive triangle the common rate is positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("triangle-heat-scaled-limit"),
                DeclarationHandle.Create(Prefix + "collocated_difference_limit"),
                H("Nonzero right-hand limit of the scaled difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive s and distinct c₁ and c₂, as ε tends to zero from above "
                    + "the scaled difference tends to one quarter of the difference of the "
                    + "exponentials with arguments −2c₁s and −2c₂s. That limit is nonzero."))),
                DescribeRole.Theorem))));
}
