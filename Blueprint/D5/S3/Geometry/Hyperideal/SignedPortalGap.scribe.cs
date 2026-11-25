using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;
internal sealed class SignedPortalGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimizing crossing count can give arbitrarily poor path length in six signed cyclic sheets.",
        H("SignedPortalGap"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-signed-shift-unbounded-gap"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/SignedPortalGap.finite_signed_shift_unbounded_gap"),
                H("An unbounded signed-portal detour"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive L, each of six sheets is a path on L+1 vertices. Reciprocal near portals of offsets zero and one give a three-crossing route at the starting base cell. The direct offset-two portal is available only at the far end, so an exactly one-crossing route costs 2L+1; the unconstrained optimum is exactly three.")),
                       Paragraph(Text("The theorem concerns a finite signed graph family. It does not assert that its members are tetrahedral manifold caps, have minimum edge degree seven, or satisfy hyperbolic angle equations. The internal shortest-distance overlay argument is classical."))),
                DescribeRole.Theorem))));
}
