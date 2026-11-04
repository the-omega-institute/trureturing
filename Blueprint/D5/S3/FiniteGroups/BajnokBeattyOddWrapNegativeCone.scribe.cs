using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyOddWrapNegativeConeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite binomial product lower bounds sharpen the negative odd-wrap cone to 25t at most 24p.",
        H("A sharper negative cone for the original odd-wrap quotients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-odd-wrap-negative-cone"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyOddWrapNegativeCone.actual_negative_odd_wrap_cone"),
                H("The original count difference is strictly negative when 25t<=24p"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let p,t be integers with p>=3 odd, t>=2 and 25t<=24p. At m=6t-1 and length (p*m).toNat, the complete original (1,9) and (3,3) quotient relation lattices have return counts W33<W19. Composite odd p and equality at the cone boundary are included.")),
                    Paragraph(Text("Set a=3pt, n=p(6t-1), A=choose(n,a), B=choose(n,a+p), and D=choose(n,a+4p). Reuse the original finite adjacent-binomial product identity choose_ratio_prod. With R=n+1 and x_i=(p+2i+1)/R for 0<=i<p, it gives A/B as the product of (1+x_i)/(1-x_i). Each x_i lies in [0,1), and their sum is exactly 2p^2/R.")),
                    Paragraph(Text("The existing logarithm lower bound at order one gives log((1+x)/(1-x))>=2x. Summing yields log(A/B)>=4p^2/R. The cone condition 25t<=24p implies 4p^2/R>=25/36. The existing six-term exponential Taylor lower bound is exactly 2905893449/1451188224 = 2+3517001/1451188224 >2, so A/B>2 and A>2B.")),
                    Paragraph(Text("The exact original count formulas give W19=2(A+D) and W33=4B. Since D is nonnegative, A>2B yields the strict original comparison without requiring an upper bound on the index of D. The proof uses finite products and exact rational bounds; it assumes no threshold, comparison, count estimate or asymptotic approximation.")),
                    Paragraph(Text("The unique threshold T therefore satisfies floor(24p/25)<T for every odd p>=3. Combining this with the positive cone t>=p gives floor(24p/25)<T<=p for odd p>=5. The integer floor is essential, and the upper endpoint is included. These estimates do not assert equality of the counts at T or an exact formula for T. The p=3 upper bound is not asserted."))),
                DescribeRole.Theorem))));
}
