using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class PositiveReferenceReplacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact loss of replacing a scalar coordinate with its normalized positive reference.",
        H("Positive reference replacement"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-reference-replacement"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Divergence/PositiveReferenceReplacement.positive_reference_replacement"),
            H("Exact loss and quadratic Klein remainder"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/mathlib2026schurcomplement")),
            Blocks(Paragraph(Text(
                "Let C be positive definite on a nonempty finite coordinate space. Suppose λ, u and a "
                + "are positive and F ≥ uC in Löwner order. Write b = Re Tr C, c = b + λ, τ = C/b, "
                + "F′ = F + aτ, C′ = cτ and t = Re Tr F + a. Here D(X∥Y) is the actual trace-log "
                + "pairing Re Tr X(log X − log Y).")),
                Paragraph(Text(
                    "The loss D(F∥C) + a log(a/λ) − D(F′∥C′) equals "
                    + "a[log(a/(λu)) − 1] + t log(c/b) − K − aE, where K = D(F′∥F) − a "
                    + "and E = Re Tr τ[log F − log(uC)]. The theorem proves E ≥ 0 and "
                    + "K ≥ Re Tr[(aτ)* (aτ)]/(2t), where * denotes the adjoint. "
                    + "The resulting bound subtracts this quadratic term from the manuscript bound.")),
                Paragraph(Text(
                    "Positive scaling gives log C′ = log C + log(c/b)I and log(uC) = log C + log(u)I. "
                    + "The trace-one identity for τ then gives the exact formula. Operator monotonicity "
                    + "and the positive trace pairing give E ≥ 0. Both F and F′ are bounded by tI, "
                    + "so the spectral-ceiling strong Klein inequality gives the quadratic remainder."))),
            DescribeRole.Theorem))));
}
