using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeArenas;

internal sealed class FourthFifthArenasDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeArenas/FourthFifthArenas.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite typed arenas for contextual meanings and causal models.",
        H("Fourth and Fifth Information-Escape Arenas"),
        Blocks(
            Arena("context-fixed-meaning-arena", "contextArena",
                "Context-selected fixed-meaning arena", "BinaryContext", "ContextLaw"),
            Arena("intervention-counterfactual-arena", "interventionArena",
                "Intervention and counterfactual arena", "BooleanSCM", "CausalLaw"))));

    private static DocumentBlock Arena(
        string id, string declaration, string title, string state, string law) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(Disp(Call("PrimitiveLawArena", F.Id(state), F.Id(law)))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "An explicit finite equivalence supplies the executable carrier while the Law "
                    + "is stated through typed readouts and named anchors."))),
            DescribeRole.Definition);

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
