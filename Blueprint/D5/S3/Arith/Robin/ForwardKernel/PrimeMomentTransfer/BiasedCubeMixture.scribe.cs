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
                Blocks(Paragraph(Text("A finite weighted mixture of biased cube functionals is a real linear functional. It is positive when the weights are nonnegative, N is positive, and every bias value has absolute value at most sqrt(N)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("character"), DeclarationHandle.Create(Prefix + "mixture_character"),
                H("Walsh character formula"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a character on T, the value is the weighted bias moment of order |T| divided by (sqrt(N)) to the power |T|."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinct-moments"), DeclarationHandle.Create(Prefix + "mixture_distinct_moments"),
                H("Distinct-index mixture moments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any finite family of bias values and weights, the distinct-index moment of order r is the weighted r-th bias moment divided by (sqrt(N)) to the power r, times the sum of coefficient products over injective index tuples. Both refutations apply this shared identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parity"), DeclarationHandle.Create(Prefix + "odd_reduction"),
                H("Odd-coordinate reduction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Repeated sign factors cancel in pairs, leaving exactly the coordinates with odd multiplicity."))),
                DescribeRole.Theorem))));
}
