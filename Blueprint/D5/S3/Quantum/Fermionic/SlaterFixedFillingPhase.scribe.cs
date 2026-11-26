using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class SlaterFixedFillingPhaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Fermionic/SlaterFixedFillingPhase.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Slater shuffle signs at fixed filling",
        H("Slater shuffle signs at fixed filling"),
        Blocks(
            Entry("crossCount_particle_hole", "Particle and hole inversion counts",
                "For retained occupations a contained in I and discarded occupations b contained in J, count the pairs j < i in each of the four products of occupied and empty subsets. The occupied inversion count plus the count for all sites equals the sum of the two one-sided occupied counts and the hole inversion count.",
                DescribeRole.Theorem),
            Entry("Factors", "Separate phases on the supported occupations",
                "There are two integer-valued factors, one depending on the occupation of each side, whose product is the occupied shuffle sign for every pair of subsets with total size k.",
                DescribeRole.Definition),
            Entry("factors_of_extreme_filling", "Phase factorization at extreme fillings",
                "For any retained and discarded site sets, the degree-k phase factors whenever k is at most one or the sum of the two site counts is at most k plus one. A supported pair then has at most one occupied site or at most one hole. In the latter case the hole inversion count vanishes and the particle and hole identity gives the factors.",
                DescribeRole.Theorem),
            Entry("not_factors_of_alternating", "Alternating cuts at intermediate filling",
                "For disjoint retained and discarded site sets, take two sites from each side in either strictly increasing alternating order. If k is at least two and k plus two is at most the combined size, choose k minus two spectators outside the alternating sites and hold their occupations fixed. The two diagonal inversion counts of the resulting occupation rectangle differ by exactly one in total from the off-diagonal counts. Any row and column factorization would give the same product of signs along both pairs of opposite corners.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("slater-fixed-filling-phase-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
