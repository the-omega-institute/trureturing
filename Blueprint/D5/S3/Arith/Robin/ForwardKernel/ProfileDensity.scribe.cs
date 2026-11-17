using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class ProfileDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/ProfileDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lipschitz functions on the unit interval approximate every real integrable profile in L1.",
        H("Lipschitz density in L1"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-lipschitz-profile-approx"),
                DeclarationHandle.Create(Prefix + "exists_lipschitz_profile_approx"),
                H("Approximation by Lipschitz profiles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real Borel integrable profile g on (0,1) and every epsilon>0, "
                    + "there is a Borel integrable profile f that is Lipschitz on [0,1] "
                    + "and satisfies integral |g-f| < epsilon. First approximate g in L1 "
                    + "by a bounded continuous function. Approximate the latter uniformly "
                    + "on [0,1] by a polynomial, with both errors at most epsilon/3. "
                    + "The polynomial derivative is bounded on the compact interval; "
                    + "the mean value theorem gives a finite Lipschitz constant. "
                    + "The integral triangle inequality yields the strict error bound."))),
                DescribeRole.Theorem))));
}
