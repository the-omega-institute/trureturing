using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class DeterministicCompletionMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite deterministic realizations factor uniquely onto the completed state.",
        H("Deterministic Completion Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-deterministic-realizations-factor-through-the-completion"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/DeterministicCompletionMinimality."
                        + "minimal_deterministic_completion"),
                H("Finite deterministic realizations factor uniquely through the completion"),
                StatementSource.FromAuthor(MinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F update source states and q read them out. A finite implementation "
                            + "consists of a surjective state map r together with an update G and "
                            + "readout s for which both the update and readout squares commute.")),
                    Paragraph(Text(
                        "The completed carrier is the repository's canonical quotient by equality "
                            + "of complete future readout itineraries. The theorem constructs the "
                            + "factor from representatives of r-fibers and proves that the full "
                            + "itinerary factorization makes this construction independent of the "
                            + "chosen representatives.")),
                    Paragraph(Text(
                        "The resulting factor is uniquely determined, surjective, commutes with "
                            + "the canonical projection and update, and preserves the readout. Its "
                            + "surjectivity gives the displayed finite cardinal lower bound.")),
                    Paragraph(Text(
                        "The proof directly applies the repository theorem "
                            + "prediction_completion_universality and the pinned-library declarations "
                            + "Function.surjInv, Function.rightInverse_surjInv, and "
                            + "Nat.card_le_card_of_surjective. Searches found no equal or stronger "
                            + "theorem carrying all five public clauses and uniqueness together."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula MinimalityFormula()
    {
        Formula sourceType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula implementationType = F.Id("W");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula implementation = F.Id("r");
        Formula implementationUpdate = F.Id("G");
        Formula implementationReadout = F.Id("s");
        Formula factor = F.Id("h");
        Formula completion = Call("CompletedState", update, readout);
        Formula projection = Call("completionProjection", update, readout);
        Formula completionUpdate = Call("completionUpdate", update, readout);
        Formula completionReadout = Call("completionReadout", update, readout);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(sourceType, type), Comma, Sp,
            Typed(outputType, type), Comma, Sp,
            Typed(implementationType, type), Comma, RowBreak, Grp(),
            OpenBracket, Call("Finite", sourceType), CloseBracket, Comma, Sp,
            OpenBracket, Call("Finite", implementationType), CloseBracket, Comma, RowBreak, Grp(),
            Typed(update, new Formula.TypeArrow(sourceType, sourceType)), Comma, Sp,
            Typed(readout, new Formula.TypeArrow(sourceType, outputType)), Comma, RowBreak, Grp(),
            Typed(implementation, new Formula.TypeArrow(sourceType, implementationType)), Comma, Sp,
            Typed(implementationUpdate,
                new Formula.TypeArrow(implementationType, implementationType)), Comma, Sp,
            Typed(implementationReadout,
                new Formula.TypeArrow(implementationType, outputType)), Comma, RowBreak, Grp(),
            Open, Call("Surjective", implementation), Sp, Land, Sp,
            implementation, Sp, Circ, Sp, update, Sp, Eq, Sp,
            implementationUpdate, Sp, Circ, Sp, implementation, Sp, Land, Sp,
            readout, Sp, Eq, Sp,
            implementationReadout, Sp, Circ, Sp, implementation, Close, RowBreak, Grp(),
            Rightarrow, Sp,
            Open, Exists, Bang, Sp, factor, Colon, Sp,
            implementationType, Sp, To, Sp, completion, Comma, RowBreak, Grp(),
            Call("Surjective", factor), Sp, Land, Sp,
            projection, Sp, Eq, Sp, factor, Sp, Circ, Sp, implementation, Sp, Land, RowBreak, Grp(),
            factor, Sp, Circ, Sp, implementationUpdate, Sp, Eq, Sp,
            completionUpdate, Sp, Circ, Sp, factor, Sp, Land, RowBreak, Grp(),
            completionReadout, Sp, Circ, Sp, factor, Sp, Eq, Sp,
            implementationReadout, Close, Sp, Land, RowBreak, Grp(),
            Call("card", completion), Sp, Leq, Sp, Call("card", implementationType), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
