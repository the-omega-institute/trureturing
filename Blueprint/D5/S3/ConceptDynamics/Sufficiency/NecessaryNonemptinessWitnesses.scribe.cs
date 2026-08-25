using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class NecessaryNonemptinessWitnessesDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Sufficiency/NecessaryNonemptinessWitnesses.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Empty types witness both nonemptiness hypotheses required by the imported theorems.",
        H("Necessary Nonemptiness Witnesses"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("an-empty-value-type-blocks-factorization"),
                DeclarationHandle.Create(DeclarationPrefix + "nonempty_value_is_necessary"),
                H("An empty value type blocks factorization"),
                StatementSource.FromAuthor(FiberFactorizationWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Set the coupling type to Empty, the observable data type to Unit, "
                            + "and the target value type to Empty. Constancy on every fiber "
                            + "holds vacuously because there are no couplings.")),
                    Paragraph(Text(
                        "A factorization would nevertheless include a function from Unit to "
                            + "Empty. Applying that function to the unique unit value produces "
                            + "an impossible element, so target nonemptiness is necessary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("an-empty-state-type-blocks-window-sufficiency"),
                DeclarationHandle.Create(DeclarationPrefix + "nonempty_state_is_necessary"),
                H("An empty state type blocks window sufficiency"),
                StatementSource.FromAuthor(EmptyStateWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Set the state type to Empty and the observation type to Unit at "
                            + "horizon zero. The window carrier Fin(1) to Unit is inhabited, "
                            + "while the canonical target image has no member.")),
                    Paragraph(Text(
                        "The required refinement would map every zero-window value into that "
                            + "empty target image. Applying its factor to the constant unit "
                            + "window exposes an impossible state witness."))),
                DescribeRole.Theorem))));

    private static Formula FiberFactorizationWitnessFormula() =>
        Disp(Seq(
            Call(
                "FiberConstantButNotFactorizable",
                F.Id("emptyMarginals"),
                F.Id("emptyCouplingValue")),
            Dot));

    private static Formula EmptyStateWitnessFormula() =>
        Disp(Seq(Neg, Sp, F.Id("EmptyStateFiniteWindowMinimalSufficiency"), Dot));
}
