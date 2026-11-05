using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class WeightedJacobiSpecializationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/WeightedJacobiSpecialization.";
    private static readonly LibraryNoteRef Question = LibraryNoteRef.Create("D5/L/Fourier/bringmann2024periodic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete integer Jacobi sum equals its actual weighted product limit.", H("WeightedJacobiSpecialization"), Blocks(
            Paragraph(Text("This is the classical Jacobi triple product at t=q^(a+1+r), z=q^r, obtained from the existing InversionSeq207 and CubicThetaJacobi suppliers. The inequality triangularExponent(k)+k >= 0 holds for every integer, including both directions of the quadratic tail. The Laurent support construction therefore transfers the complete sum and all finite factors. The factor weights are positive when r>0; for r=0 the factor 1-X^0 is zero and the product degenerates to zero. No numerical cutoff is a hypothesis. EulerPentagonalTrisection uses the sum; EulerNineDissection uses the same actual finite-product limit.")),
            Node("0", "triangular_add_index_nonnegative", "The full integer quadratic support lies in the admissible cone.", DescribeRole.Theorem),
            Node("1", "weightedExponent", "The natural degree of the weighted integer Jacobi monomial.", DescribeRole.Definition),
            Node("2", "twice_weightedExponent", "The exact integer quadratic formula, with all casts accounted for.", DescribeRole.Theorem),
            Node("3", "J", "The specialization of the actual normalized Jacobi series.", DescribeRole.Definition),
            Node("4", "hasSum_J", "Every integer Jacobi monomial, with its original parity sign, sums to J.", DescribeRole.Theorem),
            Node("5", "finiteProduct", "The actual three Euler factor families, with positive weights when r>0 and a zero factor when r=0.", DescribeRole.Definition),
            Node("6", "tendsto_finiteProduct", "The finite products converge coefficientwise to the same complete integer sum.", DescribeRole.Theorem)
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("weightedjacobispecialization-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Question),
            Blocks(Paragraph(Text(text))), role);
}
