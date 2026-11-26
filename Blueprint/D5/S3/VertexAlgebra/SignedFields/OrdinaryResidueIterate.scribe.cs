using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.SignedFields;

internal sealed class OrdinaryResidueIterateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary local-field residue iterates at all integer indices.",
        H("Ordinary local-field residue iterates"), Blocks(
            Paragraph(Text("The residue finite-support constructions retain the Scott Carnahan vertexAlg Apache-2.0 attribution of their existing suppliers. The alternating weight uses Mathlib's forward differences and binomial-ring coefficients under Apache-2.0.")),
            Describe.Lean(DescribeId.Create("ordinary-residue-iterate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SignedFields/OrdinaryResidueIterate.residue_iterate"),
                H("Ordinary residue iteration at every integer pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For fields J, A, B on a complex module, locality of A with B at order K and J with B at order L gives two finite sums for R(R(J,A,m),B,n) at every integer m and n. The first uses R(J,R(A,B,n+i),m-i) with weight chooseSign(m,i) for i in range(max(K-n,0)). The second uses R(A,R(J,B,i),m+n-i) with weight -epsilon(m) times chooseSign(m,i) for i in range(L). Both locality hypotheses use exchange scalar one. Finite Newton reconstruction controls the contact coefficients, and the coefficientwise residue calculations use finite support on each input vector."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("alternating-iterate-weight"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/SignedFields/OrdinaryResidueIterate.alternating_iterate_weight"),
                H("Alternating binomial weight at fixed total degree"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For complex a and natural k and j, the sum of (-1)^p times choose(k,p) times Ring.choose(a+p,j) over p from 0 through k equals (-1)^k times Ring.choose(a,j-k) when k is at most j, and is zero when k exceeds j. Pascal's recurrence lowers the coefficient index at each forward difference."))), DescribeRole.Theorem))));
}
