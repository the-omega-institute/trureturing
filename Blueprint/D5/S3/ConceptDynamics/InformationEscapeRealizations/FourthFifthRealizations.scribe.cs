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
            DefinitionNode("context-realization-definition", "contextRealization",
                "Context realization",
                "The typed realization reads every context field, decides both fixed-meaning predicates, and anchors the baseline and alternate contexts."),
            TheoremNode("context-fixed-meaning-realization",
                "context_parameters_can_select_distinct_fixed_points_realization",
                "Context-selected fixed meanings certificate", ContextFormula(),
                "The certificate identifies every clause of the frozen context proposition with contextArena.Law contextRealization."),
            DefinitionNode("intervention-realization-definition", "interventionRealization",
                "Intervention realization",
                "The typed realization uses Int and CF as its intervention and counterfactual readouts and has no point anchors."),
            TheoremNode("intervention-counterfactual-realization",
                "intervention_strictly_weaker_than_counterfactual_realization",
                "Intervention is weaker than counterfactual certificate",
                InterventionFormula(),
                "The certificate identifies the frozen existential Int-versus-CF separation with interventionArena.Law interventionRealization."))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id, string declaration, string title, Formula formula, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
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

    private static Formula Member(Formula owner, string field) =>
        Seq(owner, Dot, F.Id(field));

    private static Formula Paren(Formula formula) => Seq(Open, formula, Close);

    private static Formula Tuple(params Formula[] entries)
    {
        var items = new List<Formula> { Open };
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(entries[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(Paren(clauses[index]));
        }
        return Seq([.. items]);
    }

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Seq(left, Sp, Neq, Sp, right);

    private static Formula ExistsTwoTyped(
        Formula first, Formula second, Formula type, Formula body) =>
        Seq(Exists, Sp, first, Sp, second, Colon, Sp, type, Comma, Sp, body);

    private static Formula Law(string arena, string realization) =>
        Seq(Member(F.Id(arena), "Law"), Sp, F.Id(realization));

    private static Formula Certificate(Formula statement, string arena, string realization) =>
        Disp(Seq(Paren(statement), Sp, Iff, Sp, Law(arena, realization), Dot));

    private static Formula ContextFormula()
    {
        Formula baseline = F.Id("baselineContext");
        Formula alternate = F.Id("alternateContext");
        Formula falseMeaning = Tuple(F.Id("false"), F.Id("false"), F.Id("false"));
        Formula trueMeaning = Tuple(F.Id("true"), F.Id("true"), F.Id("true"));
        Formula statement = And(
            Equal(Member(baseline, "text"), Member(alternate, "text")),
            Equal(Member(baseline, "interpretationRule"),
                Member(alternate, "interpretationRule")),
            NotEqual(Member(baseline, "readerAdmission"),
                Member(alternate, "readerAdmission")),
            NotEqual(Member(baseline, "background"), Member(alternate, "background")),
            NotEqual(Member(baseline, "evaluationGoal"),
                Member(alternate, "evaluationGoal")),
            Call("IsBinaryFixedMeaning", baseline, falseMeaning),
            Call("IsBinaryFixedMeaning", alternate, trueMeaning),
            NotEqual(falseMeaning, trueMeaning));

        return Certificate(statement, "contextArena", "contextRealization");
    }

    private static Formula InterventionFormula()
    {
        Formula first = F.Id("M");
        Formula second = F.Id("N");
        Formula statement = ExistsTwoTyped(
            first, second, F.Id("DeterministicBoolSCM"), And(
                Equal(Call("Int", first), Call("Int", second)),
                NotEqual(Call("CF", first), Call("CF", second))));
        return Certificate(statement, "interventionArena", "interventionRealization");
    }
}
