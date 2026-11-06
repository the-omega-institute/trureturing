using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class CumulativeRiemannVonMangoldtDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cumulative positive zeta zero count has the classical leading constant.",
        H("Cumulative Riemann-von Mangoldt asymptotic"),
        Blocks(Describe.Lean(
            DescribeId.Create("cumulative-count-asymptotic"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/CumulativeRiemannVonMangoldt.cumulative_count_asymptotic"),
            H("Positive zero count divided by height times log height"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Count every distinct nontrivial zeta zero with imaginary part strictly "
                    + "above zero and at most T, weighted by its analytic multiplicity. As T tends "
                    + "to infinity, this count divided by T log T tends to 1/(2 pi).")),
                Paragraph(Text("The public cumulative-count lemma in ZetaOrdinatePhaseStiffness "
                    + "supplies an error bounded by D T above a fixed threshold. Its source is "
                    + "UnconditionalCanonicalZeroData.zetaRiemannVonMangoldt. Division by T log T "
                    + "bounds the normalized error by D/log T, which tends to zero. The dyadic "
                    + "iteration is reused directly. No Riemann hypothesis is required.")),
                Paragraph(Text("This statement concerns the canonical zeta zero configuration. "
                    + "The extracted coarse-count interface is specific to that configuration."))),
            DescribeRole.Theorem))));
}
