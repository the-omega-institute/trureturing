using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.ProperBaseChange;

internal sealed class ValuativeDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Valuative Density", H("Valuative Density"),
        Blocks(
            Paragraph(Text("Proper functors and the Riemann-Zariski type space of places covering them. Homotopy quotient by one endomorphism: Wang sequence and criterion via gamma minus one. Maps from perfect b to the tilt equal maps from O_C tensor W(b). Perfect algebras, perfection, and the two-chart exact sequence forcing f|g or g|f. A_inf-structures on tilted algebras; tensor with W(b) has no p-torsion. Coefficients tensored with the maximal ideal of the tilt; the ideal is idempotent. Affine maps surjective on valuation-ring points are covers: descent along v-covers.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/ProperBaseChange/ValuativeDensity.of_affine_cover"),
                H("of_affine_cover"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let V_i ⊂ Y be finitely many relatively representable subfunctors. A subfunctor U of Y on test rings is dense for Λ if every point of Y in a valuation ring of an algebraically closed field lies in some V_i contained in U on test rings.")))))));
}
