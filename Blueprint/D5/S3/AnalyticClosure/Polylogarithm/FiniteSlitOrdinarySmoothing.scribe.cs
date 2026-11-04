using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class FiniteSlitOrdinarySmoothingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinarySmoothing.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed prefixes and exact binomial smoothing",
        H("FiniteSlitOrdinarySmoothing"), Blocks(
            Describe.Lean(DescribeId.Create("signed-prefix-margin"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Signed prefixes and exact binomial smoothing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text("The kernel is the unit invOneSubPow, whose inverse is exactly (1-X)^j. For an arbitrary real ordinary series p and endpoint L, smooth(p-C(L),1,n) is the first excess. A strictly positive radial lower bound for its convergent power series, together with eventual positivity of this excess, implies the strict binomial baseline for every fixed positive smoothing order.")),
                    Paragraph(Text("If the first excess is summable, Abel's theorem identifies its radial limit with its finite total; the positive margin makes that total positive. Otherwise shift beyond its signed prefix and use divergence of a nonnegative nonsummable tail. Restore the full finite prefix in both cases. The second partial sums then have a positive constant lower bound. Further summations dominate a positive linear function after retaining each signed prefix.")),
                    Paragraph(Text("The coefficient identity follows in the ordinary power series ring by multiplication with the geometric series. Subtracting the constant series L subtracts exactly L times choose(n+j-1,n). The theorem requires the quantitative radial margin and the power series realization of the first excess as inputs. These inputs are not inferred from an endpoint limit alone, and this theorem alone does not settle the original full Xu--Zhao event."))), DescribeRole.Theorem))));
}
