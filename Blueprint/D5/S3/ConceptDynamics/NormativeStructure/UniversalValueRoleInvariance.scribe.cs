using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class UniversalValueRoleInvarianceDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/NormativeStructure/UniversalValueRoleInvariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structural value schemas survive role relabeling, while named privilege does not.",
        H("Universal Values as Role Invariants"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("structural-universal-core-is-role-natural"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "structural_universal_core_is_role_natural"),
                H("The structural core is natural under role equivalence"),
                StatementSource.FromAuthor(RoleNaturalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An interaction norm carries separate permission, harm, and truthful-"
                            + "treatment relations. Its structural core conjoins equal standing, "
                            + "reciprocity, non-harm, and truthful treatment.")),
                    Paragraph(Text(
                        "Relabeling transports every relation together through an equivalence of "
                            + "role carriers. The theorem proves that the entire conjunction holds "
                            + "after transport exactly when it held before transport.")),
                    Paragraph(Text(
                        "Equal standing is the only clause requiring a conjugate permutation. "
                            + "The other three clauses transport their two role variables directly. "
                            + "No finiteness assumption or distinguished role is used.")),
                    Paragraph(Text(
                        "This is formal universality, not a survey claim that every person or "
                            + "culture endorses these values. It also does not decide which real "
                            + "differences are morally irrelevant and may therefore be relabeled.")),
                    Paragraph(Text(
                        "Relevant history, consent, need, or responsibility must be represented in "
                            + "the normative profile rather than erased as a role name. Repository "
                            + "search found adjacent symmetry and norm-separation results, but no "
                            + "existing declaration with this role-natural boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("structural-universal-core-is-universal"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "structural_universal_core_is_universal"),
                H("Role naturality yields universality"),
                StatementSource.FromAuthor(UniversalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Specializing the carrier equivalence to a permutation proves that every "
                            + "role renaming preserves the structural core. This fixed-point property "
                            + "is the precise sense in which the four schemas are universal here."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("named-privilege-is-not-universal"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "named_privilege_is_not_universal"),
                H("A fixed named privilege fails universality"),
                StatementSource.FromAuthor(NamedPrivilegeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A two-role model permits every interaction initiated by the role named "
                            + "false. Before relabeling, that fixed name has the asserted privilege. "
                            + "Swapping false and true transports the permission relation but leaves "
                            + "the external favorite name fixed, so the privilege fails.")),
                    Paragraph(Text(
                        "The countermodel separates structural values from identity-anchored "
                            + "preferences using the same universality test. Universality therefore "
                            + "comes from role-independent form, not from attaching a preferred "
                            + "outcome to a particular name."))),
                DescribeRole.Lemma))));

    private static Formula RoleNaturalFormula()
    {
        Formula agent = F.Id("A");
        Formula other = F.Id("B");
        Formula equivalence = F.Id("e");
        Formula norm = F.Id("N");

        return Disp(Seq(
            Forall, Sp, agent, Comma, Sp, other, Colon, Sp, F.Id("Type"), Comma, Sp,
            equivalence, Colon, Sp, Call("Equiv", agent, other), Comma, Sp,
            norm, Colon, Sp, Call("InteractionNorm", agent), Comma, RowBreak, Grp(),
            Call("StructuralUniversalCore", Call("relabel", equivalence, norm)),
            Sp, Iff, Sp, Call("StructuralUniversalCore", norm), Dot));
    }

    private static Formula UniversalFormula()
    {
        Formula agent = F.Id("A");

        return Disp(Seq(
            Forall, Sp, agent, Colon, Sp, F.Id("Type"), Comma, Sp,
            Call(
                "IsUniversalSchema",
                Call("StructuralUniversalCore", agent)),
            Dot));
    }

    private static Formula NamedPrivilegeFormula() =>
        Disp(Seq(
            Neg, Sp,
            Call(
                "IsUniversalSchema",
                Call("NamedPrivilege", F.Id("false"))),
            Dot));
}
