using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.RecordWriting;

internal sealed class TwoRegisterInformationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/RecordWriting/TwoRegisterInformation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/chung2026thermodynamicobjectivity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two binary registers reach a prescribed common mutual information at an exact bath variation cost.",
        H("The information threshold for writing two records"),
        Blocks(
            Theorem("binary-information-envelope", "J_le_g_of_bias",
                "Information bound from the two branch biases",
                "For a uniform event and a binary readout, let t be the mean of the "
                + "absolute branch biases. The information in nats is bounded by "
                + "g(t), the binary Jensen–Shannon information of conditional probabilities "
                + "min(1, 1/2+t) and min(1, 1/2+t)−t. Opposing signs maximize the "
                + "marginal entropy at fixed bias magnitudes. Convexity along the "
                + "remaining interval gives the extremal pair."),
            Theorem("unique-information-budget", "existsUnique_budget",
                "Each common threshold determines one budget",
                "For every information threshold from zero to log 2 nats there is a "
                + "unique t in the closed unit interval whose g(t) equals the threshold."),
            Theorem("two-register-information-cost", "recording_information_bound",
                "Two readouts at a common information threshold require bath variation",
                "The event is equiprobable. Each branch starts at the uniform two-bit "
                + "law and can use its own list of local baths and joint reversible "
                + "permutations. The bath variation sums the joint endpoint total "
                + "variations across bath steps with zero charge for permutations. "
                + "For t in the closed unit interval, if each output marginal carries "
                + "at least g(t) nats, the mean branch cost is at least t. The range potential bounds "
                + "the sum of the absolute bias magnitudes before any comparison "
                + "between branches."),
            Theorem("two-register-information-attainment", "recording_information_bound_sharp",
                "A controlled joint permutation attains the threshold",
                "Use the same local resets in both branches to prepare product biases "
                + "min(1, 2t) and 2t−min(1, 2t). Swap and complement both outputs in the "
                + "second branch. The two marginals each have information g(t), and the "
                + "mean bath variation is exactly t. The construction uses ideal "
                + "weight-one resets in the finite protocol model."))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);
}
