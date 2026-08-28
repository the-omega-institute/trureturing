using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class BehaviorCompletionMinimalityDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Behavior completion is the least stable refinement of a readout interface.",
        H("Behavior Completion Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("behavior-completion-minimality"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionMinimality."
                        + "behavior_completion_is_least_stable_refinement"),
                H("Behavior completion is the least stable refinement"),
                StatementSource.FromAuthor(MinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F update source states. Let q and r be surjective interfaces onto "
                            + "their effective images. Stability of r is exposed by an induced "
                            + "update, and refinement of q through r is exposed by its unique "
                            + "readout factor.")),
                    Paragraph(Text(
                        "The behavior completion is the realized range of the full future q-word. "
                            + "The theorem constructs a unique map from the effective codomain of "
                            + "r to that realized completion range whose composition with r is "
                            + "the canonical completion projection.")),
                    Paragraph(Text(
                        "Prediction completion universality first supplies a word-valued factor. "
                            + "Surjectivity of r shows every such word is realized by a source "
                            + "state, yielding the effective-range factor, and also cancels r to "
                            + "prove uniqueness.")),
                    Paragraph(Text(
                        "The frozen repository universality theorem is applied directly. It is "
                            + "not an exact bind because it omits the effective-image codomain and "
                            + "unique factor required here. Pinned Mathlib supplies range "
                            + "factorization and surjective composition cancellation."))),
                DescribeRole.Theorem))));

    private static Formula Typed(string name, Formula type) =>
        Seq(F.Id(name), Colon, Sp, type);

    private static Formula MinimalityFormula()
    {
        Formula stateType = F.Id("X");
        Formula outputType = F.Id("B");
        Formula refinedType = F.Id("R");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula refinement = F.Id("r");
        Formula induced = F.Id("G");
        Formula readoutFactor = Pi;
        Formula completionFactor = F.Id("Phi");
        Formula itineraryRange = Call("ItineraryRange", update, readout);
        Formula completion = Call("completeItinerary", update, readout);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, outputType, Comma, Sp, refinedType,
            Colon, Sp, F.Seq(F.Operatorname, F.Grp(F.Id("Type"))), Comma,
            RowBreak,
            Typed("F", new Formula.TypeArrow(stateType, stateType)), Comma, Sp,
            Typed("q", new Formula.TypeArrow(stateType, outputType)), Comma, Sp,
            Typed("r", new Formula.TypeArrow(stateType, refinedType)), Comma,
            RowBreak,
            Call("Surjective", readout), Sp, Land, Sp,
            Call("Surjective", refinement), Sp, Land,
            RowBreak,
            Open, Exists, Sp, induced, Colon, Sp,
            new Formula.TypeArrow(refinedType, refinedType), Comma, Sp,
            refinement, Sp, Circ, Sp, update, Sp, Eq, Sp,
            induced, Sp, Circ, Sp, refinement, Close, Sp, Land,
            RowBreak,
            Open, Exists, Bang, Sp, readoutFactor, Colon, Sp,
            new Formula.TypeArrow(refinedType, outputType), Comma, Sp,
            readout, Sp, Eq, Sp, readoutFactor, Sp, Circ, Sp, refinement, Close,
            Sp, Rightarrow,
            RowBreak,
            Exists, Bang, Sp, completionFactor, Colon, Sp,
            new Formula.TypeArrow(refinedType, itineraryRange), Comma, Sp,
            Call("rangeFactorization", completion), Sp, Eq, Sp,
            completionFactor, Sp, Circ, Sp, refinement, Dot,
            End, Grp(F.Id("gathered"))));
    }

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
