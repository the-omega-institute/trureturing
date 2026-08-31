using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Postprocessing;

internal sealed class PostprocessingResolutionMonotonicityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Postprocessing/PostprocessingResolutionMonotonicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic postprocessing cannot refine an identification kernel.",
        H("Postprocessing Resolution Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("postprocessing-cannot-improve-identification-resolution"),
            DeclarationHandle.Create(
                Prefix + "postprocessing_cannot_improve_identification_resolution"),
            H("Postprocessing cannot improve identification resolution"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let q be a query profile and p any deterministic postprocessing map.")),
                Paragraph(Text(
                    "States with equal q-profiles remain equal after p is applied, so every "
                        + "original profile fiber remains inside one processed fiber.")),
                Paragraph(Text(
                    "The processed kernel may be equal or larger; ordinary function "
                        + "postprocessing cannot create a distinction absent from q."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula q = F.Id("q");
        Formula p = F.Id("p");
        return Disp(Seq(
            Forall, Sp, q, Colon, Sp, Arrow(F.Id("X"), F.Id("Y")), Comma, Sp,
            p, Colon, Sp, Arrow(F.Id("Y"), F.Id("Z")), Comma, Sp,
            Call("ker", q), Sp, Subseteq, Sp,
            Call("ker", Seq(p, Sp, Circ, Sp, q)), Dot));
    }
}
