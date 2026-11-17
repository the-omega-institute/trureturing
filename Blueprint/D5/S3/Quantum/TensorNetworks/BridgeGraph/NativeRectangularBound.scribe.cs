using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeRectangularBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An arbitrary native sum of three rectangular tensor products with positive scalar column Gram and 3a < 2b satisfies 2c <= d.",
        H("The native rectangular width-three dimension bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-rectangular-bound"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeRectangularBound.bound"),
            H("Arbitrary tensor factors and positive scalar column Gram"),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let a,b,c,d be arbitrary natural dimensions, M(r) complex a-by-b matrices and " +
                    "N(r) complex d-by-c matrices, indexed by r in Fin 3. The matrix F is the sum " +
                    "of M(r) tensor N(r), with rows (i,j) in Fin a times Fin d and columns (l,m) " +
                    "in Fin b times Fin c. If lambda is real and positive, F*F=lambda I, and " +
                    "3a < 2b, then 2c <= d. There is no factor-independence assumption. Every zero " +
                    "dimension is included, with the c=0 case immediate.")),
                Paragraph(Text(
                    "When 2a<b, the stronger existing native scalar-Gram obstruction gives 3c<=d. " +
                    "In the remaining range, choose an exact tensor decomposition of minimal width " +
                    "k at most three. A linear dependence on either side would remove a term, so " +
                    "both factor families are independent. Scaling one family by the reciprocal " +
                    "square root of lambda gives an identity column Gram without changing k.")),
                Paragraph(Text(
                    "For c>0, the normalized Hilbert-Schmidt Gram H(r,s)=trace(N(r)*N(s))/c " +
                    "is positive definite. Factor H=B*B and mix the M family by B, the N family " +
                    "by the inverse transpose of B. This preserves the native tensor sum. Taking " +
                    "a partial trace of its column Gram shows that the new M stack is an isometry. " +
                    "Widths zero and one contradict the dimension bound for this injective stack. " +
                    "At width two, the strict inequality 2b>3a and the product-rank inequalities " +
                    "make the entire coefficient-compression map injective. Every opposite Gram " +
                    "block is then the identity coefficient block, so concatenation has 2c " +
                    "orthonormal columns in dimension d.")),
                Paragraph(Text(
                    "At width three, the generic common-plane theorem gives a single neutral " +
                    "complex coefficient plane L for the whole Hermitian compression kernel. " +
                    "For each opposite complex Gram block, subtract its identity block and split " +
                    "the result into Hermitian real and imaginary parts. Both compress to zero " +
                    "and use this same L. Their complex recombination therefore vanishes on L " +
                    "as a full sesquilinear pairing. Choosing an orthonormal basis V of L and " +
                    "restricting the concatenated N Gram by V tensor I_c produces an identity " +
                    "Gram on Fin 2 times Fin c. Its rank is 2c and cannot exceed d. This proof " +
                    "uses the tensor Gram blocks throughout; the ambient inequality bc<=ad " +
                    "alone does not yield the conclusion."))),
            DescribeRole.Theorem))));
}
