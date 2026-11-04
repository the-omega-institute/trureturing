using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Golay;

internal sealed class RealLatticeGramDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Golay/RealLatticeGram.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral Gram data from a positive even selfdual real lattice", H("Integral Gram data from a positive even selfdual real lattice"),
        Blocks(
            Node("claim-1", "selfdual_span_gram_isUnit_det", "The dual basis produces an integer inverse",
                "A nondegenerate symmetric bilinear form and a selfdual integer basis span yield an integral inverse of the integral Gram matrix. The integer coordinates of the bilinear dual basis give a right inverse, so its determinant is a unit. No determinant value is assumed.", DescribeRole.Theorem),
            Node("claim-2", "exists_latticeData_of_real_selfdual", "A real lattice becomes actual integral charge data",
                "For a discrete full real lattice with a positive definite symmetric form, selfduality and even norms, the native integer basis extends over the reals. Its integral Gram matrix is positive definite and even, with unit determinant. The supplied integer charge linear equivalence is the actual basis map into the same real lattice, and it preserves every pairing.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
