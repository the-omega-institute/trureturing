using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class CommitmentNormativeMemoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Different committed permissions at one physical endpoint require normative memory.",
        H("Commitment Produces Normative Memory"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "committed-permissions-do-not-factor-through-physical-state"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/NormativeStructure/CommitmentNormativeMemory."
                        + "committed_permissions_do_not_factor_through_physical_state"),
                H("Committed permissions do not factor through physical state"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, Gamma, Comma, Sp, F.Id("X"), Comma, Sp,
                    F.Id("A"), Colon, Sp, Operatorname, Grp(F.Id("Type")),
                    Comma, RowBreak, Grp(),
                    F.Id("e"), Colon, Sp, Gamma, Sp, To, Sp, F.Id("X"),
                    Comma, Sp, Pi, Underscore, Grp(F.Id("P")), Colon, Sp,
                    Gamma, Sp, To, Sp, Operatorname, Grp(F.Id("Set")),
                    Open, F.Id("A"), Close, Comma, RowBreak, Grp(),
                    GammaLower, Comma, Sp, GammaLower, Apos, Colon, Sp, Gamma,
                    Comma, RowBreak, Grp(),
                    Open,
                    F.Id("e"), Open, GammaLower, Close, Sp, Eq, Sp,
                    F.Id("e"), Open, GammaLower, Apos, Close, Sp, Land, Sp,
                    Pi, Underscore, Grp(F.Id("P")), Open, GammaLower, Close,
                    Sp, Neq, Sp,
                    Pi, Underscore, Grp(F.Id("P")), Open,
                    GammaLower, Apos, Close,
                    Close, Sp, Rightarrow, RowBreak, Grp(),
                    Neg, Sp, Open,
                    Exists, Sp, F.Id("q"), Colon, Sp, F.Id("X"), Sp, To, Sp,
                    Operatorname, Grp(F.Id("Set")), Open, F.Id("A"), Close,
                    Comma, Sp,
                    Pi, Underscore, Grp(F.Id("P")), Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("compose")), Open,
                    F.Id("q"), Comma, Sp, F.Id("e"), Close,
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The history carrier, physical endpoint map, and committed future-"
                            + "permission readout are independent public source primitives on "
                            + "the canonical concept carrier.")),
                    Paragraph(Text(
                        "Two public histories have the same physical endpoint and different "
                            + "committed permission sets. The conclusion directly denies every "
                            + "physical-state-only factorization of that readout.")),
                    Paragraph(Text(
                        "The exact frozen family theorem for history-sensitive evaluation is "
                            + "imported and applied directly; no endpoint, permission readout, "
                            + "or factorization target is locally redefined."))),
                DescribeRole.Theorem))));
}
