using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourVacuumC2AlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Algebra on the Norm-Four Vacuum C2 Quotient.",
        H("Actual Algebra on the Norm-Four Vacuum C2 Quotient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normfourvacuumc2algebra-quotientproduct"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientProduct"),
                H("Descended coefficient product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D,a,s with B(a,a)=4 and s squared equal to one: The bilinear map on the existing quotient induced by the actual minus-one coefficient on S. Both argument kernels follow from the full actual commutator identities."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourvacuumc2algebra-quotientring"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientRing"),
                H("Existing quotient ring"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D,a,s with B(a,a)=4 and s squared equal to one: The commutative ring whose addition is the existing quotient addition, whose product is quotientProduct, and whose unit is the actual vacuum class. Associativity follows from the complete actual iterate formula."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourvacuumc2algebra-quotientalgebra"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.quotientAlgebra"),
                H("Compatible complex algebra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D,a,s with B(a,a)=4 and s squared equal to one: The complex algebra supplied by the existing complex module and the descended bilinear product, with scalars mapping to scalar multiples of vacuum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normfourvacuumc2algebra-actual-vacuum-c2-algebra"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourVacuumC2Algebra.actual_vacuum_c2_algebra"),
                H("Actual Algebra on the Norm-Four Vacuum C2 Quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite integral symmetric even-diagonal lattice D, charge a with B(a,a)=4, and complex s with s squared equal to one, let S be the span of all finite negative Virasoro words on the actual vacuum. Let C be the inverse image in S of the span of u_(-2)v with both u and v in S. The existing additive quotient S/C carries a commutative associative unital ring and a complex algebra compatible with its existing module. Its multiplication sends the classes of u and v to the class of the actual coefficient u_(-1)v, and its unit is the vacuum class. The quotient is finite dimensional of dimension three."))),
                DescribeRole.Theorem),
            Paragraph(Text("The complete mode commutator at p=-1,q=-2 proves that multiplication by any actual state of S preserves C2. Every correction is a higher negative product of two states in S, so the left-state derivative theorem places it in literal C2. The commutator at p=q=-1 applied to the vacuum proves commutativity modulo C2 and hence preservation in the other argument.")),
            Paragraph(Text("The complete iterate formula at r=n=-1 proves associativity modulo C2. The first family at index zero is the desired iterated product; every positive-index term in that family, and every term of the second family, is a higher negative product in C2. Both finite-support families are consumed. The bilinear map then descends through both actual kernels by liftQ₂. Vacuum creation supplies the unit. The commutative ring reuses the existing additive group, and Algebra.ofModule reuses the existing complex scalar action. The dimension theorem is consumed from NormFourVacuumC2Exact.")),
            Paragraph(Text("This is a realization of the classical C2 algebra construction in the actual lattice carrier, in the context of Li, Abelianizing vertex algebras, Corollary 3.6 and Proposition 3.7. The norm-four vector retains its Dong-Mason-Zhu and Shimakura attribution. No C2 ideal, associativity, basis, positivity or rootlessness premise is added. The companion module identifies the algebra with truncated polynomials. Rationality, Zhu algebra, fusion, analytic CFT and string realization remain outside this result.")))));
}
