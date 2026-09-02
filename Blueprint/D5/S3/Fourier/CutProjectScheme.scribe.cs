using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class CutProjectSchemeDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Fourier/CutProjectScheme.modelSet_inter";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The algebraic core of a cut-and-project construction selects physical model sets from internal windows and preserves window intersections.",
        H("Cut-and-Project Schemes"),
        Blocks(Describe.Lean(
            DescribeId.Create("model-sets-preserve-binary-window-intersections"),
            DeclarationHandle.Create(Declaration),
            H("Model sets preserve binary window intersections"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A scheme stores an additive subgroup of physical times internal space and requires physical projection to be injective on its lattice carrier.")),
                Paragraph(Text(
                    "An internal window selects lattice points, whose physical projections form the model set.")),
                Paragraph(Text(
                    "Physical injectivity identifies the two lattice witnesses arising from membership in two model sets. Their shared internal coordinate then lies in the window intersection."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula physical = F.Id("Physical");
        Formula internalSpace = F.Id("Internal");
        Formula scheme = F.Id("scheme");
        Formula left = F.Id("left");
        Formula right = F.Id("right");
        Formula setInternal = Call("Set", internalSpace);
        Formula modelSet(Formula window) => Call("modelSet", scheme, window);
        Formula intersection(Formula first, Formula second) =>
            Call("inter", first, second);

        Formula assumptions = new Formula.Logic(
            Call("AddGroup", physical),
            FormulaLogicOperator.And,
            Call("AddGroup", internalSpace));
        Formula conclusion = new Formula.Relation(
            modelSet(intersection(left, right)),
            FormulaRelationOperator.Equal,
            intersection(modelSet(left), modelSet(right)));
        Formula parameters = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("scheme"),
                    Call("Scheme", physical, internalSpace)),
                new Formula.BoundVariable(FormulaIdentifier.Create("left"), setInternal),
                new Formula.BoundVariable(FormulaIdentifier.Create("right"), setInternal),
            ],
            conclusion);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("Physical"), F.Id("Type")),
                new Formula.BoundVariable(FormulaIdentifier.Create("Internal"), F.Id("Type")),
            ],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, parameters)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
