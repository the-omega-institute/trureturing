using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CDSO;

internal sealed class LocalizationBootstrapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CDSO/LocalizationBootstrap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed-surplus-h actual-array localization and two-stage bootstrap target for CDSO Lemma 13.5.",
        H("CDSO fixed-surplus localization and bootstrap"),
        Blocks(
            Paragraph(Text(
                "The source is CDSO incidence moments and capacity phases, Definitions 1.1 and 13.1–13.2 and Lemmas 13.4–13.5. "
                + "One JointArray is the sole law: it assigns nonnegative mass to every nonempty subset of Fin (a+1+h), has total mass one, "
                + "positive actual marginals and mean cardinality a. Its K, H and d are computed from that same mass function. "
                + "A TailChoice contains any tied-allowed h-smallest-marginal set and its exact minimum relation.")),
            Describe.Lean(
                DescribeId.Create("cdso-array-data"),
                DeclarationHandle.Create(Prefix + "JointArray"),
                H("One actual finite incidence array"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "JointArray preserves the original law on all nonempty subsets, normalization, nonnegative masses, positive actual marginals, "
                    + "and the single actual expectation EK=a. No separate marginal vector, support condition, independence premise, certificate, "
                    + "near-minimizer premise, or graph condition is introduced."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cdso-producer-target"),
                DeclarationHandle.Create(Prefix + "Lemma134ProducerStatement"),
                H("Actual common-tail producer target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the faithful Lemma 13.4 producer surface: the common tail event, the exact tail and core quantities, and the minimum-marginal bounds. "
                    + "It is retained as an explicit producer obligation; prose does not count as its proof."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cdso-lemma-13-5-target"),
                DeclarationHandle.Create(Prefix + "Lemma135Statement"),
                H("Faithful full Lemma 13.5 target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For fixed h≥2 and M>0, along integer a≥4 tending to infinity, every actual JointArray family with d≤M a^(3/2) "
                        + "and every tied-allowed h-smallest TailChoice has delta→0. Eventually p,u=O_{h,M}(a^(−3/2)) and H_D=O_{h,M}(a^(3/2)), "
                        + "with constants independent of the array and the choice.")),
                    Paragraph(Text(
                        "The target retains the exact lower chain d≥H_D+(2a^3−C_{h,M}a^2)p≥h^2/p+(2a^3−C_{h,M}a^2)p, "
                        + "with the same actual event and no added localization, support, certificate, minimizer, singleton, independence or graph premise. "
                        + "The present StageA delivery records this statement and its actual producer inputs; the proof closure remains open."))),
                DescribeRole.Definition)),
        []));
}
