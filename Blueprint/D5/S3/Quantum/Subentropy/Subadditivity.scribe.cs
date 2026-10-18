using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class SubadditivityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/Subadditivity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subentropy is subadditive for every finite bipartite density state.",
        H("Subadditivity of subentropy"), Blocks(
            Paragraph(Text("Datta, Dorlas, Jozsa and Benatti state: \"Conjecture 1. Subentropy is subadditive: Q(ρAB) ≤ Q(ρA) + Q(ρB).\" The locator is arXiv:1310.1312v1, §2.3.1, Conjecture 1.")),
            Paragraph(Text("Zhang, Singh and Pati restate the unresolved question at arXiv:1510.08859v2 §7.1: \"At present, we do not know wether the subadditivity inequality of subentropy is true or not\".")),
            Describe.Lean(DescribeId.Create("subentropy-subadditive"),
                DeclarationHandle.Create(Owner + "subentropy_subadditive"),
                H("Subentropy is subadditive"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("For every pair of finite coordinate types A and B and every density state ρ on A×B, subentropy ρ ≤ subentropy (marginalRight ρ) + subentropy (marginalLeft ρ). marginalRight traces out B and retains A; marginalLeft traces out A and retains B. No rank, nonzero-probability or nondegenerate-spectrum assumption is imposed. The trace-one condition itself excludes empty state spaces.")),
                    Paragraph(Text("The pinching gap is convex on density matrices. Decompose a matrix spectrally into weighted normalized pure states. For a pure state, rectangular Gram invariance identifies its pinching gap with the classical subentropy of its block norm squares. Concavity of classical subentropy then bounds the original gap by the classical subentropy of the block trace weights. This is an actual joint decomposition of one density matrix throughout.")),
                    Paragraph(Text("For arbitrary positive blocks Y_x of total trace one, form the rectangular map V whose block columns are sqrt(Y_x). Then VV-adjoint=Σ_x Y_x and block pinching of V-adjoint V is the direct sum of Y_x. Rectangular Gram invariance and the pinching upper bound yield Q(directSum Y)≤Q(ΣY)+Q_cl((tr Y_x)_x). The construction includes zero blocks without normalization.")),
                    Paragraph(Text("Change ρ locally into an eigenbasis of its A marginal. The positive diagonal blocks sum to its original B marginal, and their traces are exactly the A marginal's eigenvalues. Nonnegative pinching gap gives Q(ρ)≤Q(pinched ρ), the preceding classical-quantum bound gives the required upper bound, and unitary invariance identifies the classical eigenvalue subentropy with Q(ρ_A). All marginals arise from the same joint state.")),
                    Paragraph(Text("The functional is the canonical determinant-integral subentropy. The StrongSubadditivityRefutation.SubentropyLike specification requires continuity on all finite density states, unitary invariance and the paper's distinct positive spectral formula. Its identification theorem subentropyLike_eq proves that every such family equals subentropy, including repeated and zero eigenvalues. Thus the canonical theorem applies to the paper's subentropy and to every family satisfying that specification."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("datta-dorlas-jozsa-benatti-2014-subentropy-subadditivity"),
                    ResolutionKind.Proved)))));
}
