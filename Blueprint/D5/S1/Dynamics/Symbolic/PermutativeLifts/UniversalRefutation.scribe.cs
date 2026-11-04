using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic.PermutativeLifts;

internal sealed class UniversalRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Topology/kang2026lifts");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single base refutes the general minimal branch.",
        H("A single base refutes the general minimal branch"),
        Blocks(
            Describe.Lean(DescribeId.Create("construction"), DeclarationHandle.Create(Owner + "claim"),
                H("Construction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The claim quantifies over all finite discrete alphabets with at least two letters and all nonempty minimal two-sided subshifts, and asserts the existence of a length at least two and a bipermutative code whose complete inverse image is minimal. Its literal negation follows from the single explicit infinite binary factorial subshift: every allowed length and every such code have a nonminimal whole lift. This settles only the general minimal branch specified in the problem dossier. Unique ergodicity and the optional Toeplitz hypothesis are not conclusions of this formal result. Priority remains unestablished; the coboundary mechanism has prior literature."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("main-result"), DeclarationHandle.Create(Owner + "result"),
                H("Result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The claim quantifies over all finite discrete alphabets with at least two letters and all nonempty minimal two-sided subshifts, and asserts the existence of a length at least two and a bipermutative code whose complete inverse image is minimal. Its literal negation follows from the single explicit infinite binary factorial subshift: every allowed length and every such code have a nonminimal whole lift. This settles only the general minimal branch specified in the problem dossier. Unique ergodicity and the optional Toeplitz hypothesis are not conclusions of this formal result. Priority remains unestablished; the coboundary mechanism has prior literature."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("kang-jager-2026-universal-permutative-lift-refutation"), ResolutionKind.Refuted))),
            [ DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/UniversalLiftSplitting")) ]));
}
