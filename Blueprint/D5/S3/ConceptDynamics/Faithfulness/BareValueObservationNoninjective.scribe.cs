using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Faithfulness;

internal sealed class BareValueObservationNoninjectiveDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Faithfulness/BareValueObservationNoninjective."
            + "bare_value_observation_not_injective";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The value-only observation identifies distinct structural completion certificates.",
        H("Bare Value Observation Is Nonfaithful"),
        Blocks(Describe.Lean(
            DescribeId.Create("bare-value-observation-is-not-injective"),
            DeclarationHandle.Create(Declaration),
            H("The bare value observation is not injective"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A ConstCert retains its completion-problem role, complex value, and proof "
                        + "of the corresponding completion equation. The value observation "
                        + "deliberately returns only the complex number.")),
                Paragraph(Text(
                    "The Gaussian Fourier certificate uses the repository theorem that the "
                        + "positive self-dual Gaussian has scale pi. The rotation certificate "
                        + "uses the pinned identity exp(pi i) = -1. Their roles are distinct, "
                        + "while both value observations are pi, so the projection is not "
                        + "injective."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula value = F.Id("val");
        Formula certificate = F.Id("ConstCert");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula typedValue = Seq(
            value, Colon, Sp, certificate, Sp, To, Sp, complex);

        return Disp(Seq(
            Neg, Sp, Call("Injective", typedValue), Dot));
    }
}
