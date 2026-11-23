using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class CommonPivotOmissionExchangeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/CommonPivotOmissionExchange";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral exchange of sparse omission constraints on alternating forms.",
        H("Exchange at a Common Pivot"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("common-pivot-omission-kernel"),
                DeclarationHandle.Create(Module + ".kernel"),
                H("Constrained alternating forms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The module consists of alternating forms whose insertions with the pivot vector and the weighted vector both vanish, and whose values are killed by the modulus."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("common-pivot-omission-exchange"),
                DeclarationHandle.Create(Module + ".common_pivot_omission_exchange"),
                H("Exchange of disjoint omission constraints"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a common pivot and a nonzero off-pivot weight in a finite ordered basis."
                    + " Take a positive modulus."
                    + " Suppose the new omitted coordinate set meets each prior set in at most its size minus two indices."
                    + " The product of the unrestricted and jointly restricted form modules is integrally linearly equivalent to the product of the two individually restricted modules."
                    + " At every prime power, a basis change localizes the insertion and the new constraint can be exchanged inside its disjoint coordinate support."
                    + " Coprime decomposition then gives the integral equivalence."))),
                DescribeRole.Theorem))));
}
