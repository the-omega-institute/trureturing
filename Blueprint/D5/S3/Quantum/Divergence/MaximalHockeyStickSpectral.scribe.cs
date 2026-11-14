using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickSpectralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickSpectral.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spectral cuts detect commutation on the common interior",
        H("Spectral cuts detect commutation on the common interior"), Blocks(
            Paragraph(Text("The spectral argument retains repeated eigenvalues, endpoint eigenspaces, zero projections and empty finite matrix spaces. These are repository geometric derivations; HMT supplies the divergence question, while GGJ supplies an antecedent for common-support localization.")),
            Node("thresholdPositive", "thresholdPositive D t is the continuous functional calculus of x -> max(x-t(1-x),0). Threshold.canonical_residuals identifies it as the left residual of the canonical scalar minimum.", false, false),
            Node("thresholdNegative", "thresholdNegative D t is the continuous functional calculus of x -> max(t(1-x)-x,0). It is the right residual, and its sandwich with the compressed weight is the threshold optimality obstruction.", false, false),
            Node("all_thresholds_iff_commute", "For Hermitian D,W whose nonzero entries in a D-eigenbasis connect only eigenvalues strictly between zero and one, vanishing thresholdPositive(D,t) W thresholdNegative(D,t) for every t>0 is equivalent to WD=DW. A positive threshold separates any two unequal interior eigenvalues. The common-corner version and the faithful threshold criterion consume this exact condition.", true, false),
            Node("interiorProjection", "interiorProjection C is the functional-calculus projection onto eigenvalues in (0,1). Both zero and one eigenspaces are omitted. Corner.overlap_supported and the final original-pair commutator use this actual spectral projection.", false, false),
            Node("all_common_thresholds_iff_commute", "For arbitrary Hermitian C,W and P=interiorProjection C, vanishing thresholdPositive(C,t) (PWP) thresholdNegative(C,t) for every t>0 is equivalent to (PWP)C=C(PWP). No positivity or nonempty-corner premise is imposed here. SingularCriterion uses the result after geometric compression.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-spectral-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
