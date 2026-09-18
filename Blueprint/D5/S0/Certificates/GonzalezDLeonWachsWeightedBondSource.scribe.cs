using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class GonzalezDLeonWachsWeightedBondSourceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/GonzalezDLeonWachsWeightedBondSource.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gonzalezdeleonwachs2026weighted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A literal finite model of the weighted bond poset and its source Mobius polynomial.",
        H("Weighted Bond Poset Source Semantics"),
        Blocks(
            Describe.Lean(DescribeId.Create("weighted-bond-source-polynomial"),
                DeclarationHandle.Create(Prefix + "sourceMobiusPolynomial"),
                H("The source Mobius polynomial"),
                StatementSource.FromAuthor(SourcePolynomialFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The displayed maximal-sum notation abbreviates the Lean definition: blocks "
                        + "are connected, weights satisfy 0 <= w < block cardinality, refinement "
                        + "uses the permitted merge increment, maximal elements are selected, and "
                        + "each coefficient is the incidence-algebra Mobius value from the singleton "
                        + "weighted bottom with exponent equal to the total block weight."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("three-vertex-source-encoding-injective"),
                DeclarationHandle.Create(Prefix + "local_normal_form_to_source_injective"),
                H("The three-vertex source encoding is injective"),
                StatementSource.FromAuthor(InjectiveFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Bottom, edge-and-weight middle elements, and top weights are recovered from "
                        + "the actual weighted partition. This is an encoding theorem for the literal "
                        + "source carrier, not a replacement recurrence."))),
                DescribeRole.Theorem))));

    private static Formula SourcePolynomialFormula() => Disp(Equal(
        Call("sourceMobiusPolynomial", F.Id("G")),
        Call("maximalConnectedWeightedMuSum", F.Id("G"))));

    private static Formula InjectiveFormula() => Disp(Call(
        "Injective", Call("localNormalFormToSource", F.Id("hG"))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
