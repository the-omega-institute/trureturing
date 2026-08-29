using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class PrimeTimeCoverEquivalenceDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Budget/PrimeTimeCoverEquivalence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite observer budget through a fixed time depth is complete exactly when its "
            + "timed separation sets cover every distinct ordered state pair.",
        H("Prime-Time Cover Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("timed-readout"),
                Handle("timedReadout"),
                H("Timed observer readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At coordinate (i,n), evaluate observer i on the n-fold update of the "
                        + "state, using the canonical complete itinerary."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("timed-separation-set"),
                Handle("timedSeparationSet"),
                H("Timed separation set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The named separation set for coordinate (i,n) reuses the canonical "
                        + "observer separation set on the timed readout family."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("time-prefix-coordinates"),
                Handle("timePrefixCoordinates"),
                H("Selected prefix coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite coordinate budget is the product of selected observers with "
                        + "the natural-number range from zero through m."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("time-prefix-readout"),
                Handle("timePrefixReadout"),
                H("Joint prefix readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The dependent joint readout assembles all selected observer-time "
                        + "coordinates through the fixed depth."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("time-prefix-cover"),
                Handle("timePrefixCover"),
                H("Time-prefix separation cover"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take the union of timed separation sets over every selected observer and "
                        + "every time no greater than m."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-time-budget-injective-iff-cover"),
                Handle("prime_time_budget_injective_iff_cover"),
                H("Timed completeness is prefix coverage"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Apply the finite-budget cover equivalence to the product of J with the "
                            + "range through m. Product membership is exactly i in J and n at "
                            + "most m, so its coordinate union is the named prefix cover.")),
                    Paragraph(Text(
                        "No finiteness assumption on states or observer indices is used. At "
                            + "depth zero this recovers the untimed theorem; empty, singleton, "
                            + "identity, constant, and zero-readout cases are checked in Lean.")),
                    Paragraph(Text(
                        "The source's weighted-cover sentence is programmatic: no timed cost "
                            + "model is asserted here."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Observer/Budget/MinimumCompleteSetCover")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ObserverMemory/Prediction/ItineraryCompletion")),
        ]));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(DeclarationPrefix + name);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula index = F.Id("I");
        Formula state = F.Id("X");
        Formula outputs = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula selected = F.Id("J");
        Formula depth = F.Id("m");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula outputFamily = Seq(index, Sp, To, Sp, type);
        Formula indexedReadout = Seq(
            Forall, Sp, F.Id("i"), Colon, Sp, index, Comma, Sp,
            state, Sp, To, Sp, Call("O", F.Id("i")));
        Formula complete = Call(
            "Injective", Call("timePrefixReadout", update, readout, selected, depth));
        Formula covers = new Formula.Relation(
            Call("timePrefixCover", update, readout, selected, depth),
            FormulaRelationOperator.Equal,
            Call("statePairUniverse", state));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("I"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("X"), type),
                new Formula.BoundVariable(FormulaIdentifier.Create("O"), outputFamily),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("F"), Seq(state, Sp, To, Sp, state)),
                new Formula.BoundVariable(FormulaIdentifier.Create("q"), indexedReadout),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("J"), Call("Finset", index)),
                new Formula.BoundVariable(FormulaIdentifier.Create("m"), naturals),
            ],
            new Formula.Logic(complete, FormulaLogicOperator.Iff, covers)));
    }
}
