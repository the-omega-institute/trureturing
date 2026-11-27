using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.KroneckerLimit;

internal sealed class LogThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Log Theta", H("Log Theta"),
        Blocks(
            Paragraph(Text("Kronecker's first limit formula for any lattice, as a one-sided real limit. Teichmüller roots of unity with their norms are p-adic limits from quadratic integers. Logarithm of theta: second derivative, integrality of constant and of limit dilation quotients.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/KroneckerLimit/LogTheta.exists_log_theta"),
                H("exists_log_theta"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("In ℂ_p, θ = exp(−L) with L = O(z²), L″ = L₂ + ξ and √−d·L₂ integral. For each limit (a, N) of pairs (ιδ, ι(δδ̄)), δ ∈ 𝓞_K, the series φ(az), exp(NL − L(az)) and (NL − L(az))′ lie in 𝔬[[φ]].")))))));
}
