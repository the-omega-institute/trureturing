using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class BiasedCubeMixtureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/BiasedCubeMixture.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite mixtures of biased Boolean cubes have explicit Walsh characters and parity reductions.",
        H("Biased Boolean cube mixtures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sign"), DeclarationHandle.Create(Prefix + "sign"),
                H("Boolean sign"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sign map sends true to one and false to minus one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mixture"), DeclarationHandle.Create(Prefix + "mixtureFunctional"),
                H("Finite biased cube mixture"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite nonnegative mixture of product sign measures is represented as a real linear functional."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("character"), DeclarationHandle.Create(Prefix + "mixture_character"),
                H("Walsh character formula"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The value on a Walsh character is the weighted moment of the bias divided by the coordinate square root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parity"), DeclarationHandle.Create(Prefix + "odd_reduction"),
                H("Odd-coordinate reduction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Repeated sign factors cancel in pairs, leaving exactly the coordinates with odd multiplicity."))),
                DescribeRole.Theorem))));
}
