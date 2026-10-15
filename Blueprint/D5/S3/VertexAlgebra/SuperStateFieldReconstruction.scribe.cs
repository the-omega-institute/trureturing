using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;
internal sealed class SuperStateFieldReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/SuperStateFieldReconstruction.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed vacuum uniqueness for state fields with an explicit parity decomposition.",
        H("Relative reconstruction"),
        Blocks(
            Paragraph(Text("The coefficient clearing expansion and vacuum recurrence generalize the supplied bc proof to arbitrary complex modules. Creation, creativity, translation vacuum, covariance, parity decomposition and relative signed locality are explicit hypotheses, not a uniqueness endpoint.")),
            Describe.Lean(DescribeId.Create("vacuum-uniqueness"), DeclarationHandle.Create(Prefix + "relative_vacuum_uniqueness"), H("Vanishing from the vacuum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The proof first kills all negative vacuum coefficients, then uses the locality clearing polynomial to recover action on homogeneous states. The two supplied parity components exhaust arbitrary inputs. The actual tensor state derivative consumes this result."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-residue-modes"), DeclarationHandle.Create(Prefix + "positive_residue_modes"), H("Nonnegative residue coefficients"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The signed nonnegative residue coefficients are the coefficients of the locality clearing polynomial."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonnegative-dong"), DeclarationHandle.Create(Prefix + "nonnegative_residue_locality"), H("Signed nonnegative Dong law"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Three pairwise clearing polynomials imply a vector-independent clearing order for the signed residue against the third field."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("all-integer-dong"), DeclarationHandle.Create(Prefix + "residue_superLocal"), H("All-integer signed residue locality"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Nonnegative residues use the polynomial cancellation law. Negative residues use divided derivatives and signed normal products; their Koszul parities add."))), DescribeRole.Theorem))));
}
