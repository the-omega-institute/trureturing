using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class BesselGenericDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bessel Generic", H("Bessel Generic"),
        Blocks(
            Paragraph(Text("Names for column coordinates and projection to rows on the data. Transformation law, support and normal form of the Bessel seed of the Poincaré series.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/BesselGeneric.isGeneric_poincare"),
                H("isGeneric_poincare"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Under Filling.IsAdmissible, if jc = −(gϖ)⁻¹ (j = WeilData.j, c the scale of the grading), the Poincaré series over the rational Bessel subgroup of an algebraic form ψ of level Kc satisfies the hypotheses Grading.IsGeneric of the unfolding step on Y.")))))));
}
