using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InterventionLaws;

internal sealed class BlockInterventionalLawFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/InterventionLaws/"
            + "BlockInterventionalLawFactorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent block responses give a product post-intervention law.",
        H("Block Interventional Law Factorization"),
        Blocks(
            Paragraph(Text(
                "A block intervention and a family of block response channels determine the "
                    + "joint response through the existing block outcome map. Pushing the "
                    + "source measure through that response defines its intervention law; "
                    + "pushing through one coordinate defines the corresponding local law.")),
            Describe.Lean(
                DescribeId.Create("block-interventional-law-factorization"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "block_interventional_law_factorization"),
                H("Independent block intervention laws factor"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Probability-level block independence includes measurability of every "
                            + "intervened response and mutual independence of the finite family. "
                            + "Mathlib's finite independent-pushforward theorem then identifies "
                            + "the joint law with the product of its local pushforwards."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("single-block-factorization-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "single_block_factorization_witness"),
                H("A single block factors trivially"),
                StatementSource.FromAuthor(SingleBlockFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On a one-element block index, every measurable response family is "
                            + "mutually independent. The general theorem therefore reduces the "
                            + "joint law to the one-coordinate product law."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("empty-block-factorization-witness"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "empty_block_factorization_witness"),
                H("The empty block law is Dirac"),
                StatementSource.FromAuthor(EmptyBlockFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an empty block family, the response tuple is unique. The empty "
                            + "finite product measure is the Dirac law at that empty tuple."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("block-independence-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "block_independence_is_necessary"),
                H("A cross-block edge defeats the product law"),
                StatementSource.FromAuthor(NecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "With two fair exogenous bits, the right block copies the left block "
                            + "along a directed edge. The two responses "
                            + "are equal, so their all-true diagonal has mass one half, whereas "
                            + "the product of the two fair marginals assigns one quarter. Thus "
                            + "block independence and the product identity both fail."))),
                DescribeRole.Lemma))));

    private static Formula MainFormula()
    {
        Formula measure = Id("mu");
        Formula intervention = Id("a");
        Formula model = Id("M");
        Formula independent = Apply(
            Id("BlockIndependent"), measure, intervention, model);
        Formula factorization = Factorization(measure, intervention, model);
        return F.Disp(new Formula.Logic(
            independent, FormulaLogicOperator.Implies, factorization));
    }

    private static Formula SingleBlockFormula()
    {
        Formula measure = Id("mu");
        Formula intervention = Id("aUnit");
        Formula model = Id("MUnit");
        Formula measurable = Apply(Id("AEMeasurable"), Apply(model, intervention), measure);
        Formula independent = Apply(
            Id("BlockIndependent"), measure, intervention, model);
        Formula conclusion = new Formula.Logic(
            independent,
            FormulaLogicOperator.And,
            Factorization(measure, intervention, model));
        return F.Disp(new Formula.Logic(
            measurable, FormulaLogicOperator.Implies, conclusion));
    }

    private static Formula EmptyBlockFormula()
    {
        Formula emptyIntervention = Id("emptyIntervention");
        Formula emptyModel = Id("emptyModel");
        Formula source = Apply(Id("dirac"), Id("unit"));
        Formula emptyTuple = Id("emptyTuple");
        return F.Disp(Equal(
            Apply(Id("blockInterventionalLaw"), source, emptyIntervention, emptyModel),
            Apply(Id("dirac"), emptyTuple)));
    }

    private static Formula NecessityFormula()
    {
        Formula source = Apply(Id("uniform"), Id("BoolPair"));
        Formula intervention = Id("nullIntervention");
        Formula model = Id("directedEdgeResponse");
        Formula notIndependent = new Formula.Not(Apply(
            Id("BlockIndependent"), source, intervention, model));
        Formula lawMismatch = new Formula.Not(Factorization(source, intervention, model));
        return F.Disp(new Formula.Logic(
            notIndependent, FormulaLogicOperator.And, lawMismatch));
    }

    private static Formula Factorization(
        Formula measure,
        Formula intervention,
        Formula model) =>
        Equal(
            Apply(Id("blockInterventionalLaw"), measure, intervention, model),
            Apply(
                Id("MeasurePi"),
                Apply(Id("localInterventionalLaw"), measure, intervention, model)));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
}
