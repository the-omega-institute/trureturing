using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class SmoothnessCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smoothness Criterion", H("Smoothness Criterion"),
        Blocks(
            Paragraph(Text("Smoothness from a tangent bound and an immersed generic holomorphic family.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/SmoothnessCriterion.smooth_of_immersion"),
                H("smooth_of_immersion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let X be locally of finite type over a normal domain R ⊂ ℂ, φ a d-parameter family of complex points over R, immersive at b, with φ(b) specialising to nearby members, and a: Spec V → X extend φ(b). If the relative tangent space at the closed point of a has dimension ≤ d, X is smooth of relative dimension d on an open set containing a.")))))));
}
