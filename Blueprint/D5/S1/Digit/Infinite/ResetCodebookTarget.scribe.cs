using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class ResetCodebookTargetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/Infinite/ResetCodebookTarget.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Analytic/mathlib2026gelfandandivt");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reset codebooks, actual sources and weighted lower-memory graphs.",
        H("Reset codebook: Target"),
        Blocks(
            Node("original_root_exists_unique", "original_root_exists_unique", "original root exists unique", "For every K >= 2, n >= K and real guard threshold d, the original pruned 6/20 matrix has exactly one spectral root z in (0,1). Two low extensions from every retained vertex force its square at z=1 to have row sums at least two. Degree-6/20 comparisons give continuity and strict increase; the intermediate value theorem then gives the root.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("RootFamily", "root-family-type", "RootFamily", "The mathematical data are specified by RootFamily(K : ℕ) (d : ℝ) := ∀ n : ℕ, K≤n → {z : ℝ // D5.S1.Digit.Infinite.ResetCodebook.Transfer.OriginalSpectralRoot K n d z}.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("target6218", "target6218", "target6218", "The mathematical data are specified by target6218(anchor : Bool) (K M N : ℕ) (b d : ℝ) (hK : 2 ≤ K) (hM : 1 ≤ M) (hN : 0 < N) (hbudget : lambda-g^2*chi^K*h false < b ∧ b < lambda-g^2*chi^K*(A false/(1-rho*chi^K))) (hd : d=(lambda-b)/(g^2*chi^K)) (hreset : max (max (X false) (Y false)) d < D5.S1.Digit.Infinite.ResetCodebook.Statement.B M) (hne : (D5.S1.Digit.Infinite.ResetCodebook.Statement.codebook anchor K N d).Nonempty) (roots : RootFamily K d) : Prop := .", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("lowerRoot", "lowerRoot", "lowerRoot", "The mathematical data are specified by lowerRoot(K n : ℕ) (d : ℝ) (hK : 2 ≤ K) (hKn : K ≤ n) : ℝ := .", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("rootFamily", "root-family-value", "rootFamily", "The mathematical data are specified by rootFamily(K : ℕ) (d : ℝ) (hK : 2 ≤ K) : Statement.RootFamily K d := .", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("reset_codebook_common_realization", "reset_codebook_common_realization", "reset codebook common realization", "Fix either actual initial state, K >= 2, a reset length M >= 1, positive weight N, the strict budget window, the associated guard threshold and a nonempty complete weak codebook. All finite actual reset concatenations share a positive error margin and retain their literal high and low tails and every departure slot. Every bilateral auxiliary concatenation has the common strict high-state margin. One finite depth n >= K places all of them in the original lower graph, whose uniquely defined spectral gamma is at least log2 of the complete codebook cardinality divided by N+20+6M. Auxiliary bilateral sequences are distinct objects from the finite actual sources.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
        )));

    private static DocumentBlock Node(string declaration, string identifier, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("resetcodebooktarget-" + identifier.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
