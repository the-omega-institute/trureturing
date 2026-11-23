using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.Qubit;

internal sealed class FibonacciClippedProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile.";
    private static readonly LibraryNoteRef Certificate =
        LibraryNoteRef.Create("D5/L/Divergence/trureturing2026fibonacciclippedprofile");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-interval clipped Fibonacci qubit profile bound.",
        H("Fibonacci qubit profile"),
        Blocks(
            Node("weights", "Contrast weights", DescribeRole.Definition,
                "The three real weights are −b, −c, and d, with b = 66t − 88, c = 15t − 25, and d = 28 − 12t."),
            Node("benchmark", "Benchmark preparations", DescribeRole.Definition,
                "The first two preparations equal (1, 0) and the third equals (0, 1)."),
            Node("timeCut", "Time cuts", DescribeRole.Definition,
                "The seven endpoints are 4/3, 113/81, 22/15, 5/3, 9/5, 2, and 7/3."),
            Node("envelope", "Affine profile envelopes", DescribeRole.Definition,
                "Put w = 69t − 85. In increasing interval order the affine expressions are "
                + "b²X/d + bZ, −bcX/w − (97/100)(b+c)Y − cdZ/w, −bcX/w − bdY/w − cdZ/w, "
                + "−(53/55)bcX/w − (24/25)bdY/w, −(53/55)bcX/w − (d − (53/55)bc/w)Y, and −dX."),
            Node("excess_profile_le_envelope", "Global bound for the excess positive-part trace",
                DescribeRole.Theorem,
                "For every unit complex qubit triple, X is one minus the squared overlap of the first two "
                + "preparations and Y and Z are their respective squared overlaps with the third. "
                + "On each closed interval between successive cuts, the actual positive-part trace for the "
                + "given triple minus that of the benchmark is at most the corresponding envelope. "
                + "The first interval uses the trace–determinant quadratic, with positive benchmark trace "
                + "and b ≤ d. For later intervals, each candidate bounds the clipped branch and dominates "
                + "the square-root branch by a squared inequality. The proof assumes unit normalization "
                + "and applies also when the preparations are linearly dependent."))));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("fibonacci-clipped-profile-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Certificate), Blocks(Paragraph(Text(prose))), role);
}
