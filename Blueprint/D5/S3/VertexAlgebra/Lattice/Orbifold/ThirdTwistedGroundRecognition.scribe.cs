using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdTwistedGroundRecognitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedGroundRecognition.";
    private static readonly LibraryNoteRef TwistedCharges =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recognition of the cubic ground charge representation from a zero-momentum vector.",
        H("Cubic Ground Charge Recognition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("third-ground-recognition-intertwines"),
                DeclarationHandle.Create(Prefix + "recognitionMap_intertwines"),
                H("Extend the zero-momentum vector by charge shifts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("Extend the assignment from the momentum basis vector at p to T(s(p))w by "
                    + "finite linear combination. The product law (4.42) and the zero-momentum moving scalar "
                    + "from (4.46) give the coefficient after rewriting the sum of charges as the new section "
                    + "lift plus a moving charge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-ground-recognition-normalized-zero"),
                DeclarationHandle.Create(Prefix + "recognitionMap_normalized_zero"),
                H("Normalize at zero momentum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("The lift s(0) lies in the moving lattice. Multiply the zero basis vector "
                    + "by the inverse of its moving scalar to send it to w. Each other momentum is a section "
                    + "charge shift of zero with an invertible coefficient, which gives uniqueness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-ground-recognition-equivalence"),
                DeclarationHandle.Create(Prefix + "recognition_of_irreducible"),
                H("Recognize the irreducible ground action"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("Each translate of a nonzero w is nonzero by the product of opposite "
                    + "charges. Independence of the target momentum subspaces gives injectivity when each "
                    + "translate lies in its corresponding space. Charge irreducibility gives surjectivity "
                    + "because the range is invariant and contains w. The weight spaces of (4.56) and their "
                    + "transport in Lemma 4.7 describe how the weight-space hypotheses arise in the ground "
                    + "space of (4.55)."))),
                DescribeRole.Theorem))));
}
