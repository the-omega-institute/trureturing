using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGeometry;

internal sealed class AffineBlockingBoundDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/bishnoi2017finitegrid");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Affine blocking sets over a finite field of order q have sharp minimum 2q-1.",
        H("The sharp affine-plane blocking minimum"),
        Blocks(Describe.Lean(
            DescribeId.Create("sharp-affine-plane-blocking-minimum"),
            DeclarationHandle.Create(
                "D5/S3/Geometry/FiniteGeometry/AffineBlockingBound.affine_blocking_minimum"),
            H("Meeting every affine line requires exactly 2q-1 points"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For every finite field F of cardinality q, the least "
                    + "cardinality of a finite set B in F x F that intersects every graph "
                    + "line y = m*x+b and every vertical line x = c is 2*q-1. This includes "
                    + "nonprime field orders and characteristic two. The union of the two "
                    + "coordinate axes attains the minimum.")),
                Paragraph(Text("Choose b0 in B and multiply the factors "
                    + "1-(b.1-b0.1)*u-(b.2-b0.2)*v for all other b in B. The product equals "
                    + "one at (u,v)=(0,0). Each nonzero covector defines the line "
                    + "u*(x-b0.1)+v*(y-b0.2)=1. A blocking point on this line differs from "
                    + "b0 and makes one factor zero, so the product vanishes at every "
                    + "other covector.")),
                Paragraph(Text("The degree is at most |B|-1. If |B|<2*q-1, Mathlib's "
                    + "finite-field evaluation-sum theorem says the sum of the product "
                    + "over all covectors is zero. Its actual values sum to one, a "
                    + "contradiction in every field. Hence |B|>=2*q-1.")),
                Paragraph(Text("Corollary 6.8 of Bishnoi, Clark, Potukuchi and Schmitt "
                    + "states the Jamison--Brouwer--Schrijver minimum n*(q-1)+1 in "
                    + "affine dimension n. The declaration proves its exact "
                    + "two-dimensional coordinate case. It does not cover arbitrary "
                    + "incidence planes, rings, projective blocking sets or only selected "
                    + "directions; Theorem 6.1(c) of the source gives the broader "
                    + "finite-grid hyperplane-covering context."))),
            DescribeRole.Theorem))));
}
