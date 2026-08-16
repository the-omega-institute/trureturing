using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciValuesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Admissible Tribonacci words acquire real values from the Tribonacci constant.",
            H("Tribonacci Values"),
            Blocks(
                Paragraph(Text(
                    "The Tribonacci constant is constructed as a real root between one and two "
                    + "of x cubed equals x squared plus x plus one. A word is read from left to "
                    + "right with weights t^-1 through t^-Q.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-constant"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Values.tribonacciConstant"),
                    H("Tribonacci constant"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Intermediate value on the interval from one to two supplies the root; "
                        + "the accompanying bounds and cubic equation are kernel-proved."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("tribonacci-name-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Values.tribonacciNameValue"),
                    H("Tribonacci name value"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each true position contributes the corresponding negative power of the "
                        + "Tribonacci constant, giving the geometric value of an admissible name."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("indexed-tribonacci-name-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Values.indexedNameValue"),
                    H("Indexed Tribonacci name value"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The canonical prefix order splits each nontrivial level into zero, "
                        + "one-zero, and one-one-zero blocks matching the three-term count."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("ordered-small-level-gap-validation"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Values.adjacentNameValueGaps"),
                    H("Ordered small-level gap validation"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Executable examples in the Lean module compute every adjacent gap with "
                        + "multiplicity and order for levels two, three, and four before the "
                        + "general spectrum theorem is invoked."))),
                    DescribeRole.Definition)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Names")),
            ]));
    }
}
