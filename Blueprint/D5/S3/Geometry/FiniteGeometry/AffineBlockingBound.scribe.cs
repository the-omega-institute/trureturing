using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGeometry;

internal sealed class AffineBlockingBoundDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/bishnoi2017finitegrid");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All nonzero linear functional fibres in a finite-field plane have sharp blocking minimum 2q-1.",
        H("The sharp affine-plane blocking minimum"),
        Blocks(Describe.Lean(
            DescribeId.Create("sharp-affine-plane-blocking-minimum"),
            DeclarationHandle.Create(
                "D5/S3/Geometry/FiniteGeometry/AffineBlockingBound.affine_blocking_minimum"),
            H("Meeting every affine linear fibre requires exactly 2q-1 points"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("Let F be any finite field of cardinality q. A finite set B "
                    + "in F x F is blocking when, for every nonzero F-linear map phi from "
                    + "F x F to F and every c in F, some p in B satisfies phi(p)=c. The "
                    + "least possible cardinality of such a set is 2*q-1. Every direction "
                    + "and every offset, including zero, is required. The statement includes "
                    + "q=2, characteristic two and nonprime field orders.")),
                Paragraph(Text("The union of the two coordinate axes attains the minimum. "
                    + "Writing phi(x,y)=x*phi(1,0)+y*phi(0,1), a nonzero phi has at least "
                    + "one nonzero coefficient. Division by that coefficient produces a "
                    + "point on an axis in each fibre phi(p)=c. Each axis has q points, "
                    + "and their intersection consists of the origin, giving 2*q-1 points.")),
                Paragraph(Text("For the lower bound, choose b0 in a blocking set B. On "
                    + "the dual plane form the polynomial P(u,v), the product of "
                    + "1-(b.1-b0.1)*u-(b.2-b0.2)*v over b in B other than b0. At the "
                    + "zero covector P equals one. A nonzero covector (u,v) defines the "
                    + "nonzero linear map phi(x,y)=u*x+v*y. Blocking at the offset "
                    + "phi(b0)+1 supplies b distinct from b0 with phi(b-b0)=1. Its "
                    + "factor is zero, so P vanishes at every nonzero covector.")),
                Paragraph(Text("The total degree of P is at most |B|-1. If |B|<2*q-1, "
                    + "this degree is less than 2*(q-1). The finite-field evaluation-sum "
                    + "theorem then makes the sum of P over all covectors zero. The "
                    + "singleton support gives sum one, contradicting one being nonzero "
                    + "in a field. Hence every blocking set has at least 2*q-1 points.")),
                Paragraph(Text("Corollary 6.8 on page 16 of arXiv:1508.06020v2, by "
                    + "Bishnoi, Clark, Potukuchi and Schmitt, states the "
                    + "Jamison--Brouwer--Schrijver minimum n*(q-1)+1. This theorem "
                    + "establishes its n=2 case using native linear functional fibres. "
                    + "It makes no assertion about higher dimensions, arbitrary "
                    + "incidence planes, nonfield rings or projective blocking sets."))),
            DescribeRole.Theorem))));
}
