using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RealRootedPermutations;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficient orders of products of positive linear factors.",
        H("Real-rooted coefficient permutations"), Blocks(
            Describe.Lean(DescribeId.Create("real-rooted-permutation-coeffs"),
                DeclarationHandle.Create("D5/S3/Combinatorics/RealRootedPermutations/Defs.coeffs"),
                H("Coefficient sequence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite family of real parameters, coeffs r k is the coefficient of X^k in the product of the factors 1 + r i X."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("real-rooted-permutation-is-unimodal"),
                DeclarationHandle.Create("D5/S3/Combinatorics/RealRootedPermutations/Defs.IsUnimodal"),
                H("Unimodal permutation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse positions increase through the value at the final position and decrease after that value."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("real-rooted-permutation-arises"),
                DeclarationHandle.Create("D5/S3/Combinatorics/RealRootedPermutations/Defs.Arises"),
                H("Weak coefficient ordering"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Arises records a positive parameter family whose nonconstant coefficients are weakly increasing in the order specified by the permutation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("real-rooted-permutation-claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/RealRootedPermutations/Defs.claim"),
                H("Question 4.6 formal statement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The claim states that, for every finite size and permutation, weakly sortable coefficient orders are exactly the unimodal permutations."))),
                DescribeRole.Definition))));
}
