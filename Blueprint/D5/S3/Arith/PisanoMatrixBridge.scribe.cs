using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class PisanoMatrixBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar Fibonacci period is the order of the Fibonacci companion matrix.",
        H("Pisano period and Fibonacci matrix order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pisano-period-matrix-order"),
                DeclarationHandle.Create("D5/S3/Arith/PisanoMatrixBridge.pisanoPeriod_eq_matrix_order"),
                H("Exact scalar-to-matrix period bridge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural modulus n greater than one, the least positive "
                    + "period of the Fibonacci residues equals the multiplicative order "
                    + "of the matrix [[1,1],[1,0]] over ZMod n. The proof identifies the "
                    + "returning pair (F_k,F_(k+1)) with the power of the reduced golden "
                    + "unit and uses the injective golden multiplication matrix homomorphism "
                    + "to transfer return exponents exactly."))),
                DescribeRole.Theorem))));
}
