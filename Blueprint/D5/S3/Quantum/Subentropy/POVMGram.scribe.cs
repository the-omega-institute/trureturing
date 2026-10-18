using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class POVMGramDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/POVMGram.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Label-preserving Gram decomposition of a finite positive operator-valued measurement.",
        H("POVM Gram decomposition"),
        Blocks(
            Paragraph(Text("For the canonical ensemble Y_x=p_x rho_x, let V be the row of positive square roots. The coordinate block projector P_x satisfies V P_x V*=Y_x. For an arbitrary finite POVM M_x, the matrices G_x=V* M_x V are positive semidefinite, sum to V*V, and retain the measurement outcome label x. Rectangular cyclicity of the trace gives Tr(P_x G_x)=Tr(M_x Y_x), so the sum of their real traces is exactly the measurement success probability. No rank or positivity assumption beyond positive semidefiniteness is imposed on the individual ensemble or measurement matrices.")),
            Describe.Lean(DescribeId.Create("coordinate-block-projector"),
                DeclarationHandle.Create(Owner + "blockProjector"), H("Coordinate block projector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The diagonal projector retains precisely the coordinates carrying the specified classical label. The projector retains the block used in the labelled contraction and trace identities."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("labelled-povm-gram-piece"),
                DeclarationHandle.Create(Owner + "povmGramPiece"), H("Labelled positive Gram piece"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The Gram piece for outcome x is V* M_x V. The internal povm_gram_decomposition proves positivity, the exact sum, block contraction and the success-probability trace identity. The outcome label remains attached to its own coordinate block; replacing these matrices by an unlabelled decomposition would lose the success identity needed for the conditional-subentropy bound.")),
                    Paragraph(Text("The internal labelled_povm_pure_decomposition diagonalizes each G_x separately. Its weights are the nonnegative eigenvalues, its vectors are unit eigenvectors, and the total weight is one. Zero eigenvalues remain zero weights on unit vectors, with no division by an eigenvalue or trace. The resulting label-indexed pure-state sum reconstructs G and has weighted block mass equal to the same success probability."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conditional-subentropy-guessing-bound"),
                DeclarationHandle.Create(Owner + "cq_conditional_subentropy_guessing"),
                H("Conditional subentropy obeys the strengthened guessing bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Datta, Dorlas, Jozsa and Benatti state at arXiv:1310.1312v1, §2.5.1, Conjecture 2:")),
                    Paragraph(Text("Conjecture 2. For a c-q state ρXB, the conditional subentropy Q(X|B) satisfies the following bound: Q(X|B) ≤ Hmin(X|B) = − ln pguess(X|B).")),
                    Paragraph(Text("For all finite ensembles with nonnegative weights summing to one, the canonical recordState and mixtureState satisfy Q(recordState)-Q(mixtureState)<=1-pGuess<=-log pGuess. Here pGuess is the supremum of the success-probability set of all positive semidefinite effects M_x summing to the identity, with success sum_x p_x Re Tr(M_x rho_x). Empty label or fragment types are excluded by ensemble normalization and the existence of a trace-one fragment state, without separate nonemptiness assumptions.")),
                    Paragraph(Text("The result uses the canonical determinant-integral subentropy. The StrongSubadditivityRefutation.subentropyLike_eq identification proves that every continuous, unitarily invariant SubentropyLike family with the paper's simple positive-spectrum formula equals this canonical value on every density state, including repeated and zero eigenvalues. Substituting that identification in the record and mixture terms transfers the same inequality to every such family; no stronger spectral or positivity hypothesis is introduced.")),
                    Paragraph(Text("The proof writes the conditional quantity as the block-pinching gap of V*V and decomposes each labelled V* M_x V into normalized eigenvectors with nonnegative eigenvalue weights. Convexity of the actual matrixSubentropy pinching gap and the label-specific pure-state estimate bound the gap by one minus this POVM's success probability. The least-upper-bound property transfers the estimate to pGuess. Its strictly positive probability bound gives log pGuess<=pGuess-1. Singular fragment states, zero weights and degenerate spectra are included, and no maximizing measurement is required."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("datta-dorlas-jozsa-benatti-2014-conditional-subentropy-guessing"),
                    ResolutionKind.Proved)))));
}
