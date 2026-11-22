using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuEndpointQuarticContractivityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tracial three-to-four contractivity of the signed two-mode Wu endpoint on positive semidefinite inputs.",
        H("Tracial contractivity at the Wu endpoint"),
        Blocks(
            Describe.Lean(DescribeId.Create("strict-contractivity"),
                DeclarationHandle.Create(Owner + "A1_quartic_contractivity_strict"),
                H("Strict contractivity for nonscalar inputs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let X be a positive semidefinite two-mode matrix that is outside the ray of nonnegative scalar multiples of the identity. The cube of the fourth normalized trace moment of the signed endpoint applied to X is strictly less than the fourth power of the third normalized trace moment of X.")),
                    Paragraph(Text("Join the mean-scaled identity to X by a segment of positive semidefinite matrices with constant normalized trace. The signed map preserves the identity and trace, so the image follows the corresponding segment. The ratio of the two moment powers starts at one. At each interior point its derivative has the opposite sign of the Euler expression bounded below by the quartic floor. The input variance there is the variance of X times the square of the segment parameter, so the floor is strictly positive. The mean value theorem gives the strict endpoint inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("contractivity"),
                DeclarationHandle.Create(Owner + "A1_quartic_contractivity"),
                H("Contractivity on positive semidefinite inputs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Wu),
                Blocks(
                    Paragraph(Text("For every positive semidefinite two-mode matrix X, the cube of the fourth normalized trace moment of the signed endpoint applied to X is at most the fourth power of the third normalized trace moment of X.")),
                    Paragraph(Text("This is the fixed tracial two-mode signed slice of Wu's Corollary 3.11 at beta = 0, p = 3 and r = 4, at the critical Gross-curve time. Remark 3.15 explicitly identifies the tracial case as proved.")),
                    Paragraph(Text("The Lean proof recovers this known bound from strict contractivity off the nonnegative scalar ray and the scalar calculation on the ray."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equality"),
                DeclarationHandle.Create(Owner + "A1_quartic_contractivity_eq_iff"),
                H("Equality on the nonnegative scalar ray"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a positive semidefinite two-mode matrix X the two moment powers are equal if and only if X is a nonnegative real scalar multiple of the identity. The endpoint fixes these matrices, including zero. The two powers for a scalar input both equal the twelfth power of its scalar."))),
                DescribeRole.Theorem))));
}
