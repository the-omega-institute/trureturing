using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Partitions;

internal sealed class HalvingPartitionStatisticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Partitions/HalvingPartitionStatistics.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/mazhang2026weightedhalving");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "HalvingPartitionStatistics", H("HalvingPartitionStatistics"), Blocks(
            Paragraph(Text("The full mean and variance audits are declared_validated. The residue-balance audit remains missing its complete mirrored four-slot realization and current source binding. The exact per-target records and missing evidence are listed in https://github.com/the-omega-institute/trureturing/issues/28691 under CLAUDE section 3.9. This audit exception supplies no mathematical proof or independent final acceptance.")),
            Paragraph(Text("The mean and central second moment are rational uniform averages over the actual SourceLists carrier. The finite length interval has one list per integer, giving mean m+1-R_m/2 and variance ((R_m+3)^2-1)/12 for every m≥2. Residue balance holds for every positive modulus and every two residue classes, by an actual injection with at most one overflow. The square-sum is reused directly from Mathlib Faulhaber. Alekseyev (2026), Theorem 5, Lemma 2 and Corollary 15 retain their antecedent credit; OEIS antecedents are Kimberling and Heinz. The later note is by Haobo Ma then Wenlin Zhang, CC BY 4.0. General deficit digit formulas, exact fixed-length maxima, general weighted coefficients, other partition bases, A349553 minimal inputs and general-input unimodality remain open. Existing atlas-lean and Mathlib licenses are retained; no global novelty claim is made.")),
            Node("meanLength", "Exact source declaration: noncomputable def meanLength (n : ℕ) : ℚ := (∑ p : SourceLists n, (p.val.length : ℚ)) / count n", DescribeRole.Definition),
            Node("varianceLength", "Exact source declaration: noncomputable def varianceLength (n : ℕ) : ℚ := (∑ p : SourceLists n, ((p.val.length : ℚ) - meanLength n) ^ 2) / count n", DescribeRole.Definition),
            Node("meanLength_dyadic", "Exact source declaration: theorem meanLength_dyadic (m : ℕ) (hm : 2 ≤ m) : meanLength (2 ^ m + 1) = m + 1 - (thresholdCount m : ℚ) / 2", DescribeRole.Theorem),
            Node("varianceLength_dyadic", "Exact source declaration: theorem varianceLength_dyadic (m : ℕ) (hm : 2 ≤ m) : varianceLength (2 ^ m + 1) = (((thresholdCount m : ℚ) + 3) ^ 2 - 1) / 12", DescribeRole.Theorem),
            Node("lengthResidueCount", "Exact source declaration: noncomputable def lengthResidueCount (n b r : ℕ) : ℕ := Nat.card {p : SourceLists n // p.val.length % b = r}", DescribeRole.Definition),
            Node("lengthResidueCount_balanced", "Exact source declaration: theorem lengthResidueCount_balanced (m b : ℕ) (hm : 2 ≤ m) (hb : 0 < b) (r s : Fin b) : lengthResidueCount (2 ^ m + 1) b r.val ≤ lengthResidueCount (2 ^ m + 1) b s.val + 1", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string statement, DescribeRole role) => Describe.Lean(
        DescribeId.Create("halvingpartitionstatistics-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(statement))), role);
}
