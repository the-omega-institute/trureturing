using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class CorrelationMinorNormExteriorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormExterior.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual exterior-order and real-complex norm correspondences", H("Actual exterior-order and real-complex norm correspondences"), Blocks(
            Entry("opnorm-ofreal", "opNorm_ofReal", "opNorm ofReal",
                "Real complexification preserves the actual rectangular Euclidean operator norm, including zero maps and empty finite index types.", DescribeRole.Theorem),
            Entry("sorted-singularvalues-ofreal", "sorted_singularValues_ofReal", "sorted singularValues ofReal",
                "For square real matrices the existing complex sorted singular values coincide with native real descending singular values, preserving multiplicity, zero spectrum and column-Gram normalization.", DescribeRole.Theorem),
            Entry("complex-opnorm-sorted", "complex_opNorm_sorted", "complex opNorm sorted",
                "The existing complex square SVD identifies the actual operator norm with the largest sorted singular value for every nonempty finite index type.", DescribeRole.Theorem),
            Entry("compound-order-correspondence", "compound_order_correspondence", "compound order correspondence",
                "The actual natural increasing compound and the existing supplier compound differ exactly by diagonal sign unitaries from the finite order permutations. No sign, index or ordering convention is silently identified.", DescribeRole.Theorem),
            Entry("cmninf-eq-native-product", "cmnInf_eq_native_product", "cmnInf eq native product",
                "For every real square matrix and every order h up to its size, the induced Euclidean norm of the natural increasing compound is the product of the largest h native descending singular values. This is consumed by the actual equal-dimensional CCNR proof; it is not an entrywise maximum.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/peledteenicarmicohen2021minor")),
            Blocks(Paragraph(Text(text))), role);
}
