using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class PredictionCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observation refinement induces a unique surjective map of predictive completions.",
        H("Predictive Completion under Observation Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observation-refinement-predictive-completion"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/PredictionCompletion."
                    + "observation_refinement_completion"),
                H("Refinement induces the canonical predictive quotient map"),
                StatementSource.FromAuthor(RefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose the coarse readout is obtained by applying forget to the fine "
                        + "readout. Applying forget at every time sends equality of complete fine "
                        + "itineraries to equality of complete coarse itineraries.")),
                    Paragraph(Text(
                        "The repository theorem relative_identity_refinement then gives the "
                        + "unique surjection between the two kernel quotients and its projection "
                        + "factorization. Quotient induction verifies that the same map "
                        + "intertwines the induced update and current readout.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Setoid.map_of_le, Setoid.lift_unique, "
                        + "Quotient.map, and Quotient.lift through the imported repository "
                        + "modules. Loogle and third-party searches found no declaration "
                        + "combining the relation, uniqueness, surjectivity, and both "
                        + "intertwining equations."))),
                DescribeRole.Theorem))));

    private static Formula RefinementFormula()
    {
        Formula state = F.Id("Y");
        Formula fineOutput = F.Id("O");
        Formula coarseOutput = F.Id("P");
        Formula update = F.Id("update");
        Formula fine = F.Id("fine");
        Formula coarse = F.Id("coarse");
        Formula forget = F.Id("forget");
        Formula hfactor = F.Id("hfactor");
        Formula fineItinerary = Call("completeItinerary", update, fine);
        Formula coarseItinerary = Call("completeItinerary", update, coarse);
        Formula fineKernel = Call("ker", fineItinerary);
        Formula coarseKernel = Call("ker", coarseItinerary);
        Formula projectionFine = Call("completionProjection", update, fine);
        Formula projectionCoarse = Call("completionProjection", update, coarse);
        Formula updateFine = Call("completionUpdate", update, fine);
        Formula updateCoarse = Call("completionUpdate", update, coarse);
        Formula readoutFine = Call("completionReadout", update, fine);
        Formula readoutCoarse = Call("completionReadout", update, coarse);
        Formula descend = F.Id("descend");
        Formula completedFine = Call("CompletedState", update, fine);
        Formula completedCoarse = Call("CompletedState", update, coarse);
        Formula descendType = Call("Function", completedFine, completedCoarse);
        Formula descendClauses = new Formula.Logic(
            Call("Surjective", descend),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Seq(projectionCoarse, Sp, Eq, Sp, descend, Sp, Circ, Sp, projectionFine),
                FormulaLogicOperator.And,
                new Formula.Logic(
                    Seq(descend, Sp, Circ, Sp, updateFine, Sp, Eq, Sp,
                        updateCoarse, Sp, Circ, Sp, descend),
                    FormulaLogicOperator.And,
                    Seq(readoutCoarse, Sp, Circ, Sp, descend, Sp, Eq, Sp,
                        forget, Sp, Circ, Sp, readoutFine))));
        Formula conclusion = new Formula.Logic(
            Seq(fineKernel, Sp, Subseteq, Sp, coarseKernel),
            FormulaLogicOperator.And,
            Seq(Exists, Bang, Sp, descend, Colon, Sp, descendType, Comma, Sp, descendClauses));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Y", type), Bound("O", type), Bound("P", type),
                Bound("update", Arrow(state, state)),
                Bound("fine", Arrow(state, fineOutput)),
                Bound("coarse", Arrow(state, coarseOutput)),
                Bound("forget", Arrow(fineOutput, coarseOutput)),
                Bound("hfactor", Seq(coarse, Sp, Eq, Sp, forget, Sp, Circ, Sp, fine)),
            ],
            conclusion));
    }

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
