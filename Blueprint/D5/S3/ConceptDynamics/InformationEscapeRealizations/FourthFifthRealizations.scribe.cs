using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class FourthFifthRealizationsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two frozen statements are equivalent to contextual and causal realization laws.",
        H("Fourth and Fifth Legacy Primitive Realizations"),
        Blocks(
            Realization("context-fixed-meaning-realization",
                "context_parameters_can_select_distinct_fixed_points_realization",
                "Context-selected fixed meanings", "contextArena",
                "contextParametersSelectDistinctFixedPoints", "contextRealization"),
            Realization("intervention-counterfactual-realization",
                "intervention_strictly_weaker_than_counterfactual_realization",
                "Intervention is weaker than counterfactual", "interventionArena",
                "interventionStrictlyWeakerThanCounterfactual", "interventionRealization"))));

    private static DocumentBlock Realization(
        string id, string declaration, string title, string arena,
        string statement, string realization) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(Disp(Call(
                "LegacyPrimitiveRealization", F.Id(arena), F.Id(statement), F.Id(realization)))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The equivalence binds the original finite objects to CUT, ADMIT, and anchor "
                    + "content, with a constructive backward implication."))),
            DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
