using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class NilSemigroupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplicative closure turns pointwise nilpotence into joint extinction in finite dimension.",
        H("Nil semigroups of linear endomorphisms"),
        Blocks(Describe.Lean(
            DescribeId.Create("nil-semigroup-common-annihilator"),
            DeclarationHandle.Create("D5/S1/Eigenstructure/NilSemigroup.exists_common_annihilator"),
            H("A common annihilated vector"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Let V be a nonzero finite-dimensional left vector space over a division ring K. Let S be any multiplicatively closed set of K-linear endomorphisms, each of which is nilpotent. Then there is a nonzero vector annihilated by every member of S. The family may be empty or infinite, and no identity or commutativity assumption is imposed.")),
                Paragraph(Text("If every member of S is zero, any nonzero vector is annihilated by the whole family; this also covers the empty family. Otherwise choose a nonzero member T with minimum positive rank. For each A in S, the range of TAT lies in the range of T. If TAT is nonzero, minimality forces equality of these ranges. The nilpotent operator TA would then map the nonzero range of T onto itself, a contradiction. Hence TAT vanishes for every A in S.")),
                Paragraph(Text("For a vector with Tx nonzero, consider the span of all ATx. This span is invariant under S and is killed by T. If it vanishes, Tx is the desired vector. Otherwise it is a nonzero proper invariant subspace, and induction on dimension supplies the vector inside it.")),
                Paragraph(Text("Yahaghi, Reducibility Results on Operator Semigroups, Chapter 4, Corollary 4.2.3, proves Levitzki triangularization for finite-dimensional left vector spaces over division rings. The minimum-rank argument gives the common-kernel conclusion directly."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("nil-semigroup-uniform-word-bound"),
            DeclarationHandle.Create("D5/S1/Eigenstructure/NilSemigroup.list_prod_eq_zero"),
            H("The dimension bounds all word lengths"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("For the same nil semigroup S, every list of members of S whose length is at least the dimension of V has product zero. Multiplication is actual endomorphism composition: in a list A, B, C, the operator C acts first, followed by B and A. No bound on the individual nilpotence exponents is supplied.")),
                Paragraph(Text("In positive dimension, take a nonzero common annihilated vector and quotient by its one-dimensional span. The induced family remains multiplicatively closed and nil. By induction, the tail of a sufficiently long word has image in the annihilated line; its first factor kills that image. In dimension zero every endomorphism is zero, so the conclusion also covers the empty product, which is the identity."))),
            DescribeRole.Theorem))));
}
