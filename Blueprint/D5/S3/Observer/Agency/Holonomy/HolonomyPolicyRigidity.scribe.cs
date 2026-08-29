using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Holonomy;

internal sealed class HolonomyPolicyRigidityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Agency/Holonomy/HolonomyPolicyRigidity."
            + "policy_invariant_holonomy_eq_identity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An injective policy invariant under holonomy forces trivial holonomy.",
        H("Holonomy Policy Rigidity"),
        Blocks(Describe.Lean(
            DescribeId.Create("holonomy-policy-rigidity"),
            DeclarationHandle.Create(Declaration),
            H("Holonomy Policy Rigidity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "An injective policy separates all memory states that it observes.")),
                Paragraph(Text(
                    "A holonomy that is invisible to such a policy must fix every memory state and hence equal the identity."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() =>
        Disp(Seq(
            F.Id("injective_policy_and_invariance"), Sp, Rightarrow, Sp,
            F.Id("holonomy_is_identity"), Dot));
}
