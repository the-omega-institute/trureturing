using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementGeometry;

internal sealed class LocalGlobalAtlasExactnessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementGeometry/LocalGlobalAtlasExactness."
            + "local_global_atlas_exactness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical local-global exactness is separation plus gluing, independently.",
        H("Local-Global Atlas Exactness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-global-atlas-exactness"),
                DeclarationHandle.Create(Declaration),
                H("Atlas exactness splits into independent separation and gluing clauses"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every refinement system, stateThread is the canonical map from a "
                            + "global state to its compatible inverse-limit thread. Its kernel "
                            + "being diagonal is the separation clause; its range being all "
                            + "threads is the gluing clause.")),
                    Paragraph(Text(
                        "Bijectivity is equivalent to the conjunction of those exact kernel and "
                            + "range statements. The theorem exposes the canonical map directly.")),
                    Paragraph(Text(
                        "Two explicit refinement systems on Bool establish logical independence: "
                            + "one has diagonal kernel but non-full range, and one has full range "
                            + "but non-diagonal kernel."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion"))]));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula EqualFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualFormula(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula state = F.Id("X");
        Formula system = F.Id("A");
        Formula boolType = F.Id("Bool");

        Formula Thread(Formula atlas) => Call("stateThread", atlas);
        Formula Kernel(Formula atlas) => Call("ker", Thread(atlas));
        Formula Range(Formula atlas) => Call("range", Thread(atlas));
        Formula Diagonal(Formula carrier) => Call("diagonal", carrier);
        Formula ThreadUniverse(Formula atlas) =>
            Call("univ", Call("InverseThread", atlas));

        Formula universalSystem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("A", Call("RefinementSystem", state)),
            ],
            IffFormula(
                Call("Bijective", Thread(system)),
                And(
                    EqualFormula(Kernel(system), Diagonal(state)),
                    EqualFormula(Range(system), ThreadUniverse(system)))));

        Formula injectiveOnly = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("A", Call("RefinementSystem", boolType))],
            And(
                EqualFormula(Kernel(system), Diagonal(boolType)),
                NotEqualFormula(Range(system), ThreadUniverse(system))));

        Formula surjectiveOnly = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("A", Call("RefinementSystem", boolType))],
            And(
                EqualFormula(Range(system), ThreadUniverse(system)),
                NotEqualFormula(Kernel(system), Diagonal(boolType))));

        return Disp(And(universalSystem, And(injectiveOnly, surjectiveOnly)));
    }
}
