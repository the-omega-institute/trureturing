using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalAbsoluteGradedSectorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/OriginalAbsoluteGradedSector.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full nonzero-charge on-shell original sector is two transverse copies in integral ghost degrees one and two.",
        H("Actual Original Absolute Graded Sector"),
        Blocks(
            Paragraph(Text("The only physical hypotheses are original D and H, both inverse-Gram equations, rank twenty-six, nonzero beta, the actual real Lorentzian Gram signature and chosenH plus level minus one equal to zero. choice is obtained from the actual constructedFrame, never supplied by the caller. downEquiv uses the actual physical realization and the proved absolute degree-one identification. upEquiv uses the actual HPL singleton-three realization. Each transverse space may be zero at levels with no transverse states; the conclusion is not that both degrees are nonzero at every level.")),
            Describe.Lean(DescribeId.Create("literal-full-original-boundaries"),
                DeclarationHandle.Create(Prefix + "full_unrestricted_boundary_intersection"),
                H("Literal Original Boundary Intersection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every ambient original-Q boundary lying in the original energy sector has an actual sector preimage, by the original charge-energy projection commuting with Q. The quotient boundary submodule is consequently exactly the comap of unrestricted OriginalBoundaries under fullOriginalCycle. fullOriginalInclusion is the literal natural OriginalCohomology class map and is injective. originalImageEquiv computes its actual image, not a replacement quotient with narrowed boundaries."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integral-ghost-one-projector"),
                DeclarationHandle.Create(Prefix + "ungraded_ghost_one_projector"),
                H("Degree-One Projector Is The First Copy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual existing all-integer ghostClassSplit is collapsed using the genuinely proved original vanishing in every degree except one and two. The first factor is the transverse down realization. Applying the integral ghost-one class projector then ungradedEquiv gives exactly the first transverse coordinate with zero second coordinate. No ungraded HPL equivalence alone is used to infer degree preservation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integral-ghost-two-projector"),
                DeclarationHandle.Create(Prefix + "ungraded_ghost_two_projector"),
                H("Degree-Two Projector Is The Second Copy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The second factor is the actual transferred up realization. The original integral ghost-two class projector becomes exactly zero first coordinate and the second transverse coordinate. All other original integer components vanish. The ungraded equivalence has two actual inverse identities, assembled from the original direct-sum reconstruction and the two transverse realization inverses."))),
                DescribeRole.Theorem),
            Paragraph(Text("This computes the indicated nonzero-charge on-shell absolute sector. Neutral beta-zero cohomology is unchanged. Strict positivity is claimed only for the canonical full degree-one form established in AbsolutePhysicalNoGhost. Complete source-admission enrollment, remote delivery, full string theory and the global moonshine, VOA, CFT, anomaly, fusion and AdS/CFT objective remain independent and open. The final structural assembly and transport are not separate novelty claims.")))));
}
