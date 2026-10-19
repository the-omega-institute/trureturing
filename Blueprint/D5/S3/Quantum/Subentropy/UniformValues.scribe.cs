using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class UniformValuesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Subentropy/UniformValues.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact subentropy values of the uniform two-level and four-level density matrices.",
        H("Two uniform subentropy values"),
        Blocks(
            Paragraph(Text("The index type may be any finite type with decidable equality of the stated cardinality. The diagonal entries are real scalars embedded in the complex field. Both values follow by algebraic expansion of the determinant kernel and the corresponding absolutely convergent improper scalar integrals.")),
            Describe.Lean(DescribeId.Create("subentropy-uniform-two"), DeclarationHandle.Create(Owner + "subentropy_uniformTwo"),
                H("The maximally mixed qubit"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(Paragraph(Text("If the cardinality is two, Q(I/2)=log 2−1/2. For t>0 its kernel equals 1/(t+1/2)−1/(t+1)−1/(4(t+1/2)^2)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("subentropy-uniform-four"), DeclarationHandle.Create(Owner + "subentropy_uniformFour"),
                H("The maximally mixed four-level state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(Paragraph(Text("If the cardinality is four, Q(I/4)=log 4−13/12. For t>0 its kernel equals 1/(t+1/4)−1/(t+1)−3/(8(t+1/4)^2)+1/(16(t+1/4)^3)−1/(256(t+1/4)^4). These two values determine the exact positive gap of the Bell-pair strong-subadditivity counterexample."))), DescribeRole.Theorem))));
}
