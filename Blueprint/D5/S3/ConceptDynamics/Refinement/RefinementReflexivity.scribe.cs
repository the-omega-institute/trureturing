using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class RefinementReflexivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every concept readout refines itself through the identity forgetting map.",
        H("Refinement Reflexivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("every-concept-readout-refines-itself"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/RefinementReflexivity."
                        + "refinement_reflexive"),
                H("Every concept readout refines itself"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("B"), Comma, Sp,
                    F.Id("q"), Colon, Sp, F.Id("X"), To, Sp, F.Id("B"), Comma, Sp,
                    Operatorname, Grp(F.Id("Refines")), Open,
                    F.Id("q"), Comma, Sp, F.Id("q"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Refinement is imported from the canonical concept-family module: a "
                            + "coarse readout factors through a finer one by a forgetting map.")),
                    Paragraph(Text(
                        "For a readout compared with itself, the forgetting map is the identity. "
                            + "Its factorization equation holds by reflexivity, so no duplicate "
                            + "refinement relation or auxiliary runtime type is introduced."))),
                DescribeRole.Theorem))));
}
