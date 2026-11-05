using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Laman;

internal sealed class HennebergRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Laman/HennebergRigidity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/chen2026combinatorialrigidity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both geometric Henneberg moves in the real plane, with their exact hypotheses.",
        H("HennebergRigidity"), Blocks(
            Describe.Lean(DescribeId.Create("hennebergrigidity-0"),
                DeclarationHandle.Create(Prefix + "exists_not_mem_span_singleton_dim_two"),
                H("A point outside a line"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every nonzero vector in the real plane, there exists a point outside its linear span. The span has dimension one, less than the ambient dimension two."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hennebergrigidity-1"),
                DeclarationHandle.Create(Prefix + "typeI_isInfinitesimallyRigid_extend"),
                H("Type I kernel injection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let V be finite, p a planar rigid placement of G, and a,b old vertices. If the displacement vectors q-p(a) and q-p(b) are linearly independent over the reals, then the placement on Option V sending none to q and some v to p(v) is rigid for typeI G a b. Restriction of velocities to old vertices is an injective map between the rigidity kernels."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hennebergrigidity-2"),
                DeclarationHandle.Create(Prefix + "exists_off_line_off_finite_dim_two"),
                H("Avoiding a line and a finite set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For any distinct real planar points pa,pb and any finite set S of planar points, there exists q outside S for which q-pa and q-pb are linearly independent. A finite union of proper affine subspaces cannot cover the plane."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hennebergrigidity-3"),
                DeclarationHandle.Create(Prefix + "typeI_isGenericallyRigidInj_two"),
                H("Type I preserves an injective rigid witness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite vertex type, graph with an injective planar rigid placement, and distinct old vertices a,b, typeI G a b admits an injective planar rigid placement. Choose the new point outside the old placement image and the line through the attachments."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hennebergrigidity-4"),
                DeclarationHandle.Create(Prefix + "typeII_collinear_inner_combo"),
                H("Recovering the deleted-edge equation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("In any natural dimension d and for any real s, assume q-p(a)=s times (p(b)-p(a)). For every velocity on Option V, (s-1) times the new a-edge inner product minus s times the new b-edge inner product equals s(s-1) times the old ab-edge inner product. The identity itself does not require s to avoid zero or one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hennebergrigidity-5"),
                DeclarationHandle.Create(Prefix + "typeII_isInfinitesimallyRigid_extend"),
                H("Type II kernel injection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let V be finite and p a planar rigid placement of G. Suppose alpha is real, alpha!=0, alpha!=1, q-p(a)=alpha times (p(b)-p(a)), and q-p(a),q-p(c) are linearly independent. Then the Option placement extending p by q is rigid for typeII G a b c. The collinear identity recovers the removed ab equation, and the two independent displacements make restriction of kernel velocities injective. The theorem has no old-edge premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hennebergrigidity-6"),
                DeclarationHandle.Create(Prefix + "typeII_isGenericallyRigidInj_two_of_nonCollinear"),
                H("Type II at a noncollinear placement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite graph with an injective rigid planar placement p, if p(b)-p(a) and p(c)-p(a) are linearly independent, typeII G a b c admits an injective rigid planar placement. Choose q on the ab line away from the endpoints and the finite old placement image, retaining independence from the c displacement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hennebergrigidity-7"),
                DeclarationHandle.Create(Prefix + "exists_nonCollinear_update_perturbation_dim_two"),
                H("A one-coordinate perturbation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Let V have decidable equality, pzero a planar placement, and a,b distinct from c. Assume pzero(b)-pzero(a) is nonzero and w lies outside its span. If a placement property P holds eventually as the c coordinate changes to pzero(c)+t times w near t=0, there exists a placement satisfying P with p(b)-p(a),p(c)-p(a) linearly independent. The statement imposes no finiteness hypothesis on V."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hennebergrigidity-8"),
                DeclarationHandle.Create(Prefix + "typeII_isGenericallyRigidInj_two"),
                H("Type II preserves an injective rigid witness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite V, graph G admitting an injective planar rigid placement, and pairwise distinct old vertices a,b,c, typeII G a b c admits such a placement. Openness of rigidity and injectivity allows a noncollinear perturbation before the line construction. This geometric theorem does not require G.Adj a b. The combinatorial preservation theorem for Laman counts requires that old edge, and the reverse decomposition supplies it."))), DescribeRole.Theorem)), []));
}
