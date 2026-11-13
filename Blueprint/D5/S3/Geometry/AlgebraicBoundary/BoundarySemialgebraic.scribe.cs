using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;
internal sealed class BoundarySemialgebraicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entire finite-degree boundary equations recover native semialgebraicity.",
        H("Semialgebraicity of the original full cone"),
        Blocks(Paragraph(Text("A nonzero polynomial vanishing on the entire original frontier is the only algebraic input, with arbitrary finite degree and possible interior zeros. The actual TauCeti CAD existence proof supplies a finite connected semialgebraic partition of its nonzero locus. Each connected cell avoids the whole frontier, so it lies entirely inside the original interior or outside the closed cone. Select those cells contained in the interior. This is a subfamily of a finite family; its selector need not be semialgebraic. Their union is exactly the interior with the polynomial zero set removed. Nonzero polynomial density and convex full-dimensional closure recover the same original cone as the closure of that finite union. The actual real projection instance proves that this closure is semialgebraic.")),
        Paragraph(Text("The coordinate linear homeomorphism transports the entire original ambient interior and frontier. Induction on the generated algebra returns finite Boolean combinations of polynomial equality and strict positivity conditions evaluated on the original carrier. A second output gives a condition on the signs of finitely many explicit polynomials. Neither semialgebraicity of the original cone, a finite component certificate, nor any requested producer output is an assumption. The external CAD, projection, partition and closure proofs retain their upstream ownership; this application claims no independent credit for those results.")))));
}
