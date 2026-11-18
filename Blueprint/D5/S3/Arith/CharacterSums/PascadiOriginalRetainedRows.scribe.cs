using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalRetainedRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal original rows and their actual integer-coordinate endpoint records have equal cardinality, so the dyadic moment bound applies directly to the original retained rows.",
        H("Actual retained rows in their occupied middle lattices"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-retained-original-row-realization"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalRetainedRows.actual_retained_rows_realization"),
                H("Exact realization of the original integer fibers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a nonzero modulus c, two alternating units, and any finite set T of original integer rows (a,b,w;d,v,t) in the literal widths X,Y. Every row must satisfy the existing six-return word in the unchanged order (a,t,b,d,w,v), with value minus the identity. Require both middle entries w,t and both first endpoint entries a,b to be units modulo c. The parameter set is exactly s=T.image(originalMiddle), with originalMiddle=(w,t). A reduced basis B(w,t) of the actual lattice c divides w*y-t*x is required only when (w,t) belongs to s.")),
                    Paragraph(Text("Choose the anchor coordinates from B.anchor_coordinates, representing the actual physical vector -(w,t). The original return equations put both physical endpoints (a,d),(b,v) in that same integer lattice. B.decompose supplies their actual integer coordinates. E(w,t) is the image of the original T fiber under this coordinate map. Reconstructing originalRows from each image recovers the original six integers exactly. Conversely, B.coordinates_unique makes the reconstruction map injective. Its image is exactly the original T fiber, so card(T)=sum over s of card(E(w,t)), with no collision or multiplicity loss.")),
                    Paragraph(Text("The construction also returns the actual reduced-basis vectors, anchor equality, original WordSolution, retained endpoint-unit conditions and literal endpoint boxes needed by the dyadic estimate. No basis is requested outside the finite occupied parameter set; the total coordinate functions use harmless zero extensions there. Empty T therefore needs no artificial basis at (0,0)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-original-retained-row-dyadic-count"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalRetainedRows.actual_retained_rows_dyadic_count"),
                H("The global dyadic estimate counts original rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every epsilon>0 there is C>0 uniform in prime p, positive widths 0<X<=Y with 3Y<p^2, H>0 with H^2=XY, and the original finite row set T. Under the preceding original-word, literal-box, middle-unit and endpoint-unit conditions at c=p^3, choose actual reduced bases only on s=T.image(originalMiddle). Explicitly retain the long-chart inequality p^6<XY*weightedSq(X,Y,B.R) and unit B.R.1. The internally constructed q,R,V,E then satisfy card(T)<=2 sum over s of actualRecordBadDegree(p,q,R,V,E) + sqrt(card(s) C p^epsilon (XY/p^3)^5 (1+log(2p)/log 2)).")),
                    Paragraph(Text("Apply the exact original-row realization and the existing actual_dyadic_retained_endpoint_count. All of its physical-basis, anchor, word, unit and box premises come from the original rows or the explicit chosen-basis restrictions. Transfer the exact cardinality identity to the real-valued estimate. The output preserves exact fiber reconstruction and injectivity, allowing later consumers to bound the actual bad degrees without replacing the original finite row set."))),
                DescribeRole.Theorem),
            Paragraph(Text("This closes the passage from original retained ReturnRows to the global record count. It does not bound the remaining sum of actual bad degrees or recover the removed short, nonunit or endpoint charts. Those contributions and the final full Pascadi prime-cube estimate remain separate.")))));
}
