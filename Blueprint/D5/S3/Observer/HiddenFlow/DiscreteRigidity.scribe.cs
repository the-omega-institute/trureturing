using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class DiscreteRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonzero integer-parameter hidden actions cannot extend to continuous additive real flows.",
        H("Integer Actions Obstruct Continuous Hidden Flows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonzero-integer-actions-have-no-continuous-real-extension"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/DiscreteRigidity."
                        + "nonzero_integer_action_has_no_continuous_real_extension"),
                H("Nonzero integer actions have no continuous real extension"),
                StatementSource.FromAuthor(ObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let jump be an additive integer-parameter action on the hidden address "
                            + "space. If a continuous additive real flow restricted along the "
                            + "canonical integer inclusion to jump, the frozen continuous-rigidity "
                            + "theorem would make that real flow zero. Its integer restriction "
                            + "would then be zero as well, contradicting the nonzero hypothesis.")),
                    Paragraph(Text(
                        "This establishes an obstruction for each named nonzero integer action "
                            + "itself. It does not say that every action has integer parameters, "
                            + "that every hidden-address subgroup is cyclic, that a minimal jump "
                            + "exists, or that an observer premise selects an action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "the-canonical-integer-jump-is-nonzero-and-has-no-real-extension"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/DiscreteRigidity."
                        + "discrete_hidden_jump_is_nonzero_and_has_no_continuous_real_extension"),
                H("The canonical integer jump is nonzero and has no real extension"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("discreteHiddenJump"), Sp, Neq, Sp, D(0), Sp,
                    Land, Sp, Neg, Sp, Exists, Sp, F.Id("flow"), Sp,
                    InMacro, Sp, Operatorname, Grp(F.Id("CAddHom")), Open,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Prod, Underscore,
                    Grp(F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("P"))), Sp,
                    Mathbb, Grp(F.Id("Z")), Underscore, Grp(F.Id("p")), Close,
                    Comma, Sp,
                    F.Id("flow"), Sp, Circ, Sp, F.Id("cast"), Underscore,
                    Grp(Mathbb, Grp(F.Id("Z"))), Sp, Eq, Sp,
                    F.Id("discreteHiddenJump"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The canonical jump sends each integer to its cast in every p-adic "
                            + "coordinate. Its value at one in the prime-two coordinate is one, "
                            + "so it is nonzero. Applying the preceding obstruction to this same "
                            + "map proves that no continuous additive real flow restricts to it.")),
                    Paragraph(Text(
                        "The conjunction supplies the required anti-vacuity witness and derives "
                            + "its separation from real flows from rigidity. It makes no "
                            + "crossed-product universal-property claim and no classification "
                            + "claim for other actions."))),
                DescribeRole.Theorem))));

    private static Formula ObstructionFormula()
    {
        Formula hiddenAddress = F.Id("HiddenAddress");
        Formula hiddenAddressDefinition = Seq(
            Prod, Underscore,
            Grp(F.Id("p"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("P"))), Sp,
            Mathbb, Grp(F.Id("Z")), Underscore, Grp(F.Id("p")));

        return Disp(Seq(
                    hiddenAddress, Sp, Colon, Eq, Sp, hiddenAddressDefinition,
                    Semi, Esc,
                    Forall, Sp, F.Id("jump"), Sp,
                    InMacro, Sp, Operatorname, Grp(F.Id("AddHom")), Open,
                    Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    hiddenAddress, Close,
                    Comma, Sp, F.Id("jump"), Sp, Neq, Sp, D(0), Sp,
                    Rightarrow, Sp, Neg, Sp, Exists, Sp, F.Id("flow"), Sp,
                    InMacro, Sp, Operatorname, Grp(F.Id("CAddHom")), Open,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    hiddenAddress, Close,
                    Comma, Sp,
                    F.Id("flow"), Sp, Circ, Sp, F.Id("cast"), Underscore,
                    Grp(Mathbb, Grp(F.Id("Z"))), Sp, Eq, Sp, F.Id("jump"), Dot));
    }
}
