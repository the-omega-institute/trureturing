using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentDesign;

internal sealed class StaticExactExperimentDesignDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/ExperimentDesign/StaticExactExperimentDesign."
            + "static_exact_design";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two complementary change experiments are jointly exact, and every exact static "
            + "selection contains both.",
        H("Static Exact Experiment Design"),
        Blocks(Describe.Lean(
            DescribeId.Create("static-exact-design"),
            DeclarationHandle.Create(Declaration),
            H("Both complementary experiments are necessary and sufficient"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state carrier has three model labels. The false experiment role "
                        + "detects only label one, while the true role detects only label two.")),
                Paragraph(Text(
                    "Each response alone merges two labels. Their canonical joint readout is "
                        + "injective, and an injective static selection of the two roles must "
                        + "be the full Boolean selection."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        foreach (var clause in clauses)
        {
            if (items.Count > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(clause);
        }
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula model = F.Id("m");
        Formula experiment = F.Id("e");
        Formula selection = F.Id("J");
        Formula modelType = Call("Fin", D(3));
        Formula experimentType = F.Id("Bool");
        Formula changeX = new Formula.Subscript(F.Id("E"), F.Id("X"));
        Formula changeY = new Formula.Subscript(F.Id("E"), F.Id("Y"));
        Formula readout = F.Id("q");
        Formula both = Seq(OpenBrace, F.Id("false"), Comma, Sp,
            F.Id("true"), CloseBrace);

        Formula changeXDefinition = Seq(
            Forall, Sp, Typed(model, modelType), Comma, Sp,
            Apply(changeX, model), Colon, Eq, Sp,
            Call("decide", Seq(model, Sp, Eq, Sp, D(1))));
        Formula changeYDefinition = Seq(
            Forall, Sp, Typed(model, modelType), Comma, Sp,
            Apply(changeY, model), Colon, Eq, Sp,
            Call("decide", Seq(model, Sp, Eq, Sp, D(2))));
        Formula readoutDefinition = Seq(
            Forall, Sp, Typed(experiment, experimentType), Comma, Sp,
            Typed(model, modelType), Comma, Sp,
            Apply(readout, experiment, model), Colon, Eq, Sp,
            Call("if", experiment, Apply(changeY, model), Apply(changeX, model)));

        Formula singleCollision = Seq(Open,
            Forall, Sp, Typed(experiment, experimentType), Comma, Sp,
            Neg, Call("Injective", Call("readoutAt", readout, experiment)), Close);
        Formula jointExact = Call("Injective", Call("jointReadout", readout));
        Formula selectionNecessary = Seq(Open,
            Forall, Sp,
            Typed(selection, Call("Finset", experimentType)), Comma, Sp,
            Call("Injective", Call("jointReadout", Call("restrict", readout, selection))),
            Sp, Rightarrow, Sp, selection, Sp, Eq, Sp, both, Close);

        return Disp(new Formula.Aligned([
            Seq(changeXDefinition, Comma),
            Seq(changeYDefinition, Comma),
            Seq(readoutDefinition, Comma),
            Seq(And(singleCollision, jointExact, selectionNecessary), Dot),
        ]));
    }
}
