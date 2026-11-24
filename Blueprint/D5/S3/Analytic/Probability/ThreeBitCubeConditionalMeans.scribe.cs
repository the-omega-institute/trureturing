using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class ThreeBitCubeConditionalMeansDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A conditional mean criterion for centered upper-event signs on a three-bit cube.",
        H("Conditional means on a three-bit cube"),
        Blocks(
            Describe.Lean(DescribeId.Create("three-bit-cube-conditional-means-upper-sign"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/ThreeBitCubeConditionalMeans.centered_sum_nonpos_of_antitone_fiber_means"),
                H("Every upper event has nonpositive centered sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("h"), Comma, Sp,
                    Seq(Operatorname, Grp(F.Id("AntitoneFiberMeans"))), Open, F.Id("p"), Comma, Sp, F.Id("h"), Close,
                    Sp, Rightarrow, Sp, Forall, Sp, F.Id("U"), Comma, Sp,
                    Seq(Operatorname, Grp(F.Id("IsUpperSet"))), Open, F.Id("U"), Close,
                    Sp, Rightarrow, Sp, Seq(Operatorname, Grp(F.Id("CenteredSum"))),
                    Open, F.Id("p"), Comma, Sp, F.Id("h"), Comma, Sp, F.Id("U"), Close, Sp, Leq, Sp, D(0)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take any probability mass function on the pointwise ordered three-bit cube and any real score. "
                    + "For each coordinate subset, compare the conditional score at all comparable pairs of positive-mass fibers. "
                    + "AntitoneFiberMeans denotes these comparisons. CenteredSum is the probability-weighted sum of the score "
                    + "minus its overall mean on the indicated upper set. A coordinate-face comparison gives the sign for "
                    + "upper sets contained in or containing an upper face. For the majority event, exchanging one singleton "
                    + "for one doubleton reduces the sign to the upper-face sign and two point comparisons."))),
                DescribeRole.Theorem))));
}
