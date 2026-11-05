using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;
internal sealed class ActualOddGradeOrthogonalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/ActualOddGradeOrthogonality.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Actual Form Odd Degree Orthogonality", H("Original Actual Form Odd Degree Orthogonality"), Blocks(
            Paragraph(Text("For arbitrary LatticeData D with unit integral Gram determinant, the original actualForm pairs two actual tensor eigenvectors of the existing actualTensorL0 to zero whenever their integer odd degrees u and v differ. The eigenvalues are rank/16+u/2 and rank/16+v/2. The integers may be negative, and no positive-definiteness, ground symmetry or rank restriction is added.")),
            Paragraph(Text("The proof reuses actualAmbientBasis and actualTensorL0_repr. Nonzero coordinates of an eigenvector have exactly its integer odd degree. The existing WeightedPolynomialSubstitution.eval2_totalWeight theorem proves that same-frequency finite colour mixing preserves the odd weight of each oscillator monomial. Unfolding the existing Wick form then exposes its original factorial coordinate pairing, whose two supports are disjoint. Bilinear expansion in the original tensor basis finishes the proof.")),
            Paragraph(Text("ActualChargedAdjoint.actualForm, its private Classical.choice GroundPairing, and SignedOscillatorWick.wick are unchanged. The proof uses the existing definitions by definitional reduction; it does not name mangled private declarations or introduce a second pairing. Both ground slots retain their order. Empty supports, zero vectors, repeated variables, rank zero and indefinite lattices remain in the theorem's scope.")),
            Paragraph(Text("This is a missing dependency for the original corrected dual finite-grade support argument. It supplies degree orthogonality only: corrected-field homogeneity and the subsequent dual-support argument remain separate obligations. It does not prove ground symmetry, inversion, finite charge support, representability, Monster moonshine, string theory or AdS/CFT. The result is classical graded Wick orthogonality, with no literature novelty claim.")),
            Paragraph(Text("The accompanying Reg mirror preserves the full dependent theorem telescope and has compiled variation, sensitivity and readout-dependence proofs. Its current binding remains declared_unresolved with IE-C050, source.dictionary_or_proof_coordinate; the missing recognized source classification and validation certificate are recorded at https://github.com/the-omega-institute/trureturing/issues/21259. This is an unfinished audit under the linked-issue exception, independently of the kernel-checked orthogonality theorem.")),
            Describe.Lean(DescribeId.Create("actual-form-odd-grade-orthogonal"),
                DeclarationHandle.Create(Prefix + "actualForm_oddGrade_orthogonal"),
                H("Distinct integer odd degrees are orthogonal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For all integer u and v, original actual tensor zero-mode eigenvectors x and y of those odd degrees satisfy actualForm D hu x y=0 when u differs from v. The chosen ground bilinear factor is preserved exactly."))),
                DescribeRole.Theorem))));
}
