using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal;

internal sealed class SoftInterventionModularityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite DAG mechanism modules support local kernel replacement, with modularity "
            + "required for the formula.",
        H("Soft Intervention Modularity"),
        Blocks(
            Definition(
                "mechanism-module",
                "mechanismModule",
                "Finite mechanism module",
                "A mechanism module assigns a finite parent-indexed PMF to every DAG node."),
            Definition(
                "soft-intervention",
                "softIntervention",
                "Soft intervention",
                "A soft intervention replaces exactly the selected node mechanisms and "
                    + "leaves all other mechanisms unchanged."),
            Theorem(
                "local-replacement-formula",
                "local_replacement_formula",
                "Local replacement formula",
                LocalReplacementFormula(),
                "The joint mass factors into the selected replacement kernels and the "
                    + "unchanged kernels."),
            Theorem(
                "modularity-is-necessary",
                "modularity_is_necessary",
                "Modularity is necessary",
                ModularityNecessaryFormula(),
                "A device that changes a root and its child together disagrees with the "
                    + "local formula that keeps the child mechanism fixed."))));

    private static DocumentBlock.Describe Definition(
        string id,
        string declaration,
        string heading,
        string description) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(DeclarationPrefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string description) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(DeclarationPrefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))),
            DescribeRole.Theorem);

    private static Formula LocalReplacementFormula()
    {
        Formula baseKernel = Call("base", F.Id("v"), F.Id("x"));
        Formula replacementKernel = Call("replacement", F.Id("i"), F.Id("x"));
        Formula selectedProduct = Call("prod", F.Id("i"), F.Id("I"), replacementKernel);
        Formula unchangedProduct = Call("prod", F.Id("v"), F.Id("VminusI"), baseKernel);
        Formula rhs = Seq(selectedProduct, Sp, Times, Sp, unchangedProduct);
        Formula lhs = Call(
            "jointLaw",
            Call("softIntervention", F.Id("base"), F.Id("I"), F.Id("replacement")),
            F.Id("x"));
        return Disp(new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs));
    }

    private static Formula ModularityNecessaryFormula()
    {
        Formula linked = Call("linkedJointLaw", F.Id("x"));
        Formula local = Call("localReplacementProduct", F.Id("I"), F.Id("x"));
        return Disp(new Formula.Relation(linked, FormulaRelationOperator.NotEqual, local));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
