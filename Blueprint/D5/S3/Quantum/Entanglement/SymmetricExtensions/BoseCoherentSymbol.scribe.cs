using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseCoherentSymbolDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseCoherentSymbol.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coherent symbols separate actual Bose-supported operators",
        H("Coherent symbols of Bose operators"), Blocks(
            Paragraph(Text("This is the finite polynomial spanning argument used in Gulati-Nechita-Park, Theorem 8.9. It concerns actual computational tensor matrices and the repository's full symmetric projector. It does not assume the GNP extension characterization and does not yet prove that characterization.")),
            Describe.Lean(DescribeId.Create("bose-coherent-symbol"),
                DeclarationHandle.Create(Prefix + "symbol"),
                H("Actual bihomogeneous entry polynomial"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each computational matrix entry multiplies the monomial with its row occupation in the first variable family and its column occupation in the second. Repeated occupations are summed with their actual multiplicities, without any normalization."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bose-coherent-evaluation"),
                DeclarationHandle.Create(Prefix + "eval_symbol"),
                H("Evaluation is the actual coherent quadratic form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Substituting conjugate z in the first family and z in the second gives exactly the quadratic form of the actual repeated tensor vector. This identity requires no support or positivity hypothesis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bose-coherent-separation"),
                DeclarationHandle.Create(Prefix + "eq_zero_of_coherent"),
                H("Coherent evaluations separate Bose operators"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every tensor length and local dimension, a Hermitian matrix supported by the full symmetric-projector sandwich is zero if all its coherent quadratic forms vanish. An invertible Cartesian substitution and polynomial uniqueness prove vanishing of the independent-coordinate polynomial. The existing occupation-orbit theorem then identifies each coefficient with a matrix entry times two strictly positive occupation multiplicities. Empty and zero-dimensional boundaries are retained."))), DescribeRole.Theorem))));
}
