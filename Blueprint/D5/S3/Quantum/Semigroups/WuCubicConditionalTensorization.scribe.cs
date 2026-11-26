using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicConditionalTensorizationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicConditionalTensorization.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wu’s two-mode cubic bound for arbitrary positive semidefinite first-occupation blocks.",
        H("Occupation-conditioned cubic tensorization"),
        Blocks(
            Describe.Lean(DescribeId.Create("occupation-conditional-bound"),
                DeclarationHandle.Create(Owner + "occupation_conditional_bound"),
                H("Cubic bound on occupation blocks"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Wu),
                Blocks(
                    Paragraph(Text("Use Wu v1, Remark 3.15, equation (3.54), at exponent three with r = exp(β/3). " +
                        "For r ≥ 1 and arbitrary complex positive semidefinite 2 × 2 matrices A and B, let M be " +
                        "their block diagonal in the first occupation, with the product indices swapped as in Lean, " +
                        "and set X = GInv(r) M GInv(r). With t = Re Tr(M³), the theorem bounds " +
                        "α(r)[Re Tr(M³(log(M³) − log(D(r)))) − t log t] by " +
                        "(9/8) Re Tr(M² G(r) generator(r,X) G(r)). " +
                        "The trace is ordinary and the matrix logarithms use real functional calculus. " +
                        "The statement includes r = 1, singular blocks, and zero total mass with Lean’s log(0) = 0.")),
                    Paragraph(Text("Put x = (Re Tr(A³))^(1/3), y = (Re Tr(B³))^(1/3), and γ = 9/[4(1 + r³)]. " +
                        "The conditional entropy split and the energy of the two jumps give the one-mode deficits " +
                        "at A, B, and diag(x,y), plus γr²[x²y − Re Tr(A²B)] and γr[xy² − Re Tr(AB²)]. " +
                        "WuOneModeCubic.one_mode_bound supplies the three one-mode bounds. " +
                        "Scalar Hölder with the squared overlaps of the independent eigenbases bounds both mixed traces."))),
                DescribeRole.Theorem))));
}
