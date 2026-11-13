using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RealRootedPermutations;

internal sealed class LogConcaveDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict log concavity restricts every coefficient-sorting permutation.",
        H("Sorting Positive Real-Rooted Product Coefficients"),
        Blocks(
            Describe.Lean(DescribeId.Create("strict-increase-before-selected-maximum"),
                DeclarationHandle.Create("D5/S3/Combinatorics/RealRootedPermutations/LogConcave.increasing_before_max"),
                H("Strict increase before a selected maximum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let f be a real sequence positive at every natural index through N. Suppose f(i)f(i+2) is strictly less than f(i+1) squared whenever i+2 is at most N. If m is at most N and f(i) is at most f(m) throughout that interval, then f(a) is strictly less than f(a+1) for every natural a with a+1 less than m. The step immediately into m follows weakly from maximality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strict-decrease-after-selected-maximum"),
                DeclarationHandle.Create("D5/S3/Combinatorics/RealRootedPermutations/LogConcave.decreasing_after_max"),
                H("Strict decrease after a selected maximum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same explicit positivity, strict log-concavity and maximality assumptions on a real sequence, f(a+1) is strictly less than f(a) whenever m is less than a and a+1 is at most N. The step immediately out of m follows weakly from maximality; two adjacent maximal values are allowed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-product-sorting-unimodal"),
                DeclarationHandle.Create("D5/S3/Combinatorics/RealRootedPermutations/LogConcave.unimodal_of_arises"),
                H("Every weak coefficient sorting is unimodal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any natural n, let r range over n+1 strictly positive real numbers and form the product of 1+r(i)x. If a permutation of the nonconstant coefficient indices lists their coefficients in weakly increasing order, then the inverse positions increase up to the value listed last and decrease thereafter. Coefficient indices and permutation values differ by one; the constant coefficient is omitted.")),
                    Paragraph(Text("Induction on a finite set of factors proves positivity through the degree, vanishing above the degree, and strict log concavity at every interior index. Multiplication by 1+sx sends c(k+1) to c(k+1)+s c(k). Expansion of the resulting log-concavity difference gives two adjacent differences and a nonnegative middle term. The lowest interior index is handled separately, using the positive constant coefficient.")),
                    Paragraph(Text("For a positive strictly log-concave sequence, a weak decrease forces the next decrease to be strict, and this propagates to the end of the sequence. Consequently the indices strictly below a selected maximum form a strictly increasing sequence, and those strictly above it form a strictly decreasing sequence. The final position of a weak sorting is a maximum. Comparisons away from that position are therefore strict; comparisons involving it follow from the final-position property. This includes a possible tie between two adjacent maximal coefficients."))),
                DescribeRole.Theorem))));
}
