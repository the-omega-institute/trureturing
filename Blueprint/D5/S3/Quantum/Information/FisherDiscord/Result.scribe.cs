using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.FisherDiscord;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/liluozhang2025fisherdiscord");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-qubit flagged state refutes partial-trace monotonicity of Fisher discord.",
        H("Partial trace can increase Fisher discord"), Blocks(
            Describe.Lean(DescribeId.Create("fisher-discord-result"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/FisherDiscord/Result.result"),
                H("Explicit refutation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Use the diagonal qubit state with weights one fifth and four fifths and the Pauli X observable. Its Fisher discord is four twenty-fifths for every Hermitian SLD solution. Explicit Hermitian solutions establish existence on both spaces. The flagged state with support on the basis vectors 00 and 11 has the same marginal and zero discord for the lifted observable, for every Hermitian SLD solution. The necessary condition for diagonal marginals then contradicts the universal partial-trace inequality."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("li-luo-zhang-2025-fisher-discord-partial-trace-refutation"),
                    ResolutionKind.Refuted)))));
}
