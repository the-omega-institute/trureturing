using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class LandauerIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reservoir and unitary entropy balances determine the exact heat-entropy-information identity.",
        H("The Exact Heat-Entropy-Information Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-heat-entropy-information-identity-from-balances"),
                DeclarationHandle.Create(
                    "D5/S3/DivergenceSupport/LandauerIdentity.landauer_identity_from_balances"),
                H("The two entropy balances imply the exact identity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp,
                    F.Id("beta"), Comma, Sp,
                    F.Id("heat"), Comma, Sp,
                    F.Id("systemEntropyChange"), Comma, Sp,
                    F.Id("reservoirEntropyChange"), Comma, Sp,
                    F.Id("mutualInformation"), Comma, Sp,
                    F.Id("reservoirDivergence"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    F.Id("beta"), Sp, Cdot, Sp, F.Id("heat"), Sp, Eq, Sp,
                    F.Id("reservoirEntropyChange"), Sp, Plus, Sp,
                    F.Id("reservoirDivergence"), Sp, Rightarrow, RowBreak,
                    F.Id("mutualInformation"), Sp, Eq, Sp,
                    F.Id("systemEntropyChange"), Sp, Plus, Sp,
                    F.Id("reservoirEntropyChange"), Sp, Rightarrow, RowBreak,
                    F.Id("beta"), Sp, Cdot, Sp, F.Id("heat"), Sp, Eq, Sp,
                    Minus, F.Id("systemEntropyChange"), Sp, Plus, Sp,
                    F.Id("mutualInformation"), Sp, Plus, Sp,
                    F.Id("reservoirDivergence"), Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The reservoir balance expresses inverse temperature times released heat " +
                        "as the reservoir entropy change plus its divergence remainder. The unitary " +
                        "entropy balance expresses final mutual information as the sum of the system " +
                        "and reservoir entropy changes.")),
                    Paragraph(Text(
                        "Eliminating the shared reservoir entropy change gives the displayed exact " +
                        "identity. No sign assumption is used and no remainder is discarded. The " +
                        "formal module also checks concrete witnesses showing that both balance " +
                        "hypotheses are satisfiable and that each is necessary for this derivation."))),
                DescribeRole.Theorem
            )),
        []));
}
