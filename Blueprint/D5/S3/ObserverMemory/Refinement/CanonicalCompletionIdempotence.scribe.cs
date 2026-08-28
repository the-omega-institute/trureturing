using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class CanonicalCompletionIdempotenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Predictive completion is canonically idempotent.",
        H("Canonical Completion Idempotence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("canonical-completion-idempotence"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/CanonicalCompletionIdempotence."
                        + "canonical_completion_idempotence"),
                H("The second completion is canonically equivalent to the first"),
                StatementSource.FromAuthor(IdempotenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A predictive completion is the quotient by equality of every future "
                            + "readout value, with its update and current readout induced from "
                            + "the source dynamics.")),
                    Paragraph(Text(
                        "Completing that induced readout a second time produces the second-stage "
                            + "future relation. The existing cascade-completion construction "
                            + "supplies its canonical equivalence with the direct completion.")),
                    Paragraph(Text(
                        "The Lean declaration exposes that equivalence itself, rather than only "
                            + "an inhabitation claim, by applying the repository's exact "
                            + "cascadeCompletionEquiv theorem with the identity forgetting map.")),
                    Paragraph(Text(
                        "Repository search found the exact canonical declaration "
                            + "cascadeCompletionEquiv; it is imported and applied directly."))),
                DescribeRole.Definition))));

    private static Formula IdempotenceFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula update = F.Id("update");
        Formula readout = F.Id("readout");
        Formula identity = F.Id("id");
        Formula secondRelation = Call("secondStageRelation", update, readout, identity);
        Formula completedState = Call("CompletedState", update, readout);
        Formula conclusion = Seq(
            Call("Quotient", secondRelation), Sp, Equiv, Sp, completedState);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Y", TypeUniverse()),
                Bound("O", TypeUniverse()),
                Bound("update", Arrow(state, state)),
                Bound("readout", Arrow(state, output)),
            ],
            Seq(conclusion, Dot)));
    }

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

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

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
