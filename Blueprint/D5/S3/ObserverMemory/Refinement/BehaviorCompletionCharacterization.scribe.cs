using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class BehaviorCompletionCharacterizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal stable completion is uniquely equivalent to canonical completion.",
        H("Behavior Completion Characterization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("behavior-completion-characterization"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/BehaviorCompletionCharacterization."
                        + "behavior_completion_characterization"),
                H("The universal stable completion is canonical"),
                StatementSource.FromAuthor(CharacterizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let candidate be an effective interface for the source state: it is "
                            + "surjective, its update is stable under the source update, and its "
                            + "readout preserves the original readout. Assume further that every "
                            + "effective stable refinement factors uniquely through candidate.")),
                    Paragraph(Text(
                        "The canonical completed-state projection is itself an effective stable "
                            + "refinement preserving the readout, so universality supplies the map "
                            + "back to candidate. A surjective choice of representatives supplies "
                            + "the forward map. Their projection equations make them inverse, and "
                            + "surjectivity proves uniqueness of the resulting equivalence.")),
                    Paragraph(Text(
                        "The canonical completion declarations and the existing prediction "
                            + "universality theorem are imported from the ObserverMemory family. "
                            + "The finite minimality theorem is not an exact hit. Repository and "
                            + "pinned-Mathlib searches found no theorem combining all premises "
                            + "with the unique canonical equivalence."))),
                DescribeRole.Theorem))));

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

    private static Formula CharacterizationFormula()
    {
        Formula candidateState = F.Id("W");
        Formula refinementState = F.Id("V");
        Formula update = F.Id("u");
        Formula readout = F.Id("r");
        Formula candidate = F.Id("c");
        Formula candidateUpdate = F.Id("U");
        Formula candidateReadout = F.Id("R");
        Formula refinement = F.Id("v");
        Formula refinementUpdate = F.Id("S");
        Formula refinementReadout = F.Id("s");
        Formula factor = F.Id("f");
        Formula equivalence = F.Id("e");
        Formula completion = Call("Completion", update, readout);
        Formula projection = Call("Projection", update, readout);

        Formula candidateConditions = Seq(
            Call("Surjective", candidate), Sp, Land, Esc,
            candidate, Sp, Circ, Sp, update, Sp, Eq, Sp,
            candidateUpdate, Sp, Circ, Sp, candidate, Sp, Land, Esc,
            readout, Sp, Eq, Sp, candidateReadout, Sp, Circ, Sp, candidate);
        Formula refinementConditions = Seq(
            Call("Surjective", refinement), Sp, Land, Esc,
            refinement, Sp, Circ, Sp, update, Sp, Eq, Sp,
            refinementUpdate, Sp, Circ, Sp, refinement, Sp, Land, Esc,
            readout, Sp, Eq, Sp, refinementReadout, Sp, Circ, Sp, refinement);
        Formula universality = Seq(
            Forall, Sp, refinementState, Comma, Sp, refinement, Comma, Sp,
            refinementUpdate, Comma, Sp, refinementReadout, Comma, Esc,
            Open, refinementConditions, Close, Sp, Rightarrow, Sp,
            Exists, Bang, Sp, factor, Colon, Sp, refinementState, Sp, To, Sp,
            candidateState, Comma, Sp,
            candidate, Sp, Eq, Sp, factor, Sp, Circ, Sp, refinement);

        return Disp(Seq(
            Forall, Sp, candidateState, Comma, Sp, update, Comma, Sp, readout,
            Comma, Sp, candidate, Comma, Sp, candidateUpdate, Comma, Sp,
            candidateReadout, Comma, Esc,
            Open, candidateConditions, Close, Sp, Land, Esc,
            Open, universality, Close, Sp, Rightarrow, Esc,
            Exists, Bang, Sp, equivalence, Colon, Sp,
            Call("Equiv", candidateState, completion), Comma, Sp,
            projection, Sp, Eq, Sp, equivalence, Sp, Circ, Sp, candidate, Dot));
    }
}
