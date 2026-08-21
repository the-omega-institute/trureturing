using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class RefinementTransitivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refinement witnesses compose through the intermediate readout carrier.",
        H("Refinement Transitivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinement-witnesses-compose"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/RefinementTransitivity."
                        + "refinement_transitive"),
                H("Refinement witnesses compose"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Refines")), Open, F.Id("q1"), Comma,
                    Sp, F.Id("q2"), Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("Refines")), Open, F.Id("q"), Comma,
                    Sp, F.Id("q1"), Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("Refines")), Open, F.Id("q"), Comma,
                    Sp, F.Id("q2"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The canonical refinement relation is factorization through a "
                            + "forgetting map.")),
                    Paragraph(Text(
                        "Composing the two source factorization witnesses produces the "
                            + "factor from the finest readout directly to the coarsest."))),
                DescribeRole.Theorem))));
}
