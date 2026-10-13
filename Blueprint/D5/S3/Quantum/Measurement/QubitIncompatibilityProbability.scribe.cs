using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class QubitIncompatibilityProbabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/QubitIncompatibilityProbability.";

    private static readonly LibraryNoteRef Zhang = LibraryNoteRef.Create("D5/L/QuantumBounds/zhang2019incompatibilityprobability");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The qubit incompatibility probability is strictly less than one quarter.",H("Qubit Incompatibility Probability"), Blocks(
        Node("result","One-quarter conjecture refuted","The exact probability is nine times a four-dimensional cube integral. The inequality sqrt(1-z) ≤ 1-z/2-z²/8 on [0,1], together with three explicit moments, gives the upper bound 5910272/23648625 < 1/4. Thus the probability in Section III.C of Zhang et al. differs from one quarter.",DescribeRole.Theorem,
            new Formula.Not(Q("OrderedRootCoordinates","claim")),AssessedProvenance.FromRepo(Zhang),
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("zhang-et-al-2019-qubit-incompatibility-probability"), ResolutionKind.Refuted))
        ),[]));

    private static Formula X(string n) => F.Id(n);

    private static Formula Q(string owner, string n) => Seq(Operatorname, Grp(X(owner), Dot, X(n)));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role,
        Formula formula, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
