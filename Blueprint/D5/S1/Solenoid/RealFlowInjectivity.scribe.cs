using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class RealFlowInjectivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The universal-solenoid real flow is faithful.",
        H("Universal-Solenoid Real-Flow Injectivity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-real-time-maps-to-zero-exactly-when-it-is-zero"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/RealFlowInjectivity.realFlow_eq_zero_iff"),
                H("The real flow has trivial kernel"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("t"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Esc, Sp,
                    F.Id("realFlow"), Open, F.Id("t"), Close, Sp, Eq, Sp, D(0),
                    Sp, Iff, Sp, F.Id("t"), Sp, Eq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If the flow vanishes, then at every positive modulus its coordinate "
                            + "t divided by that modulus is an integer modulo one. Choose a "
                            + "natural modulus larger than the absolute value of t. The "
                            + "corresponding integer has absolute value below one, hence is "
                            + "zero, and division by the positive modulus forces t to vanish. "
                            + "The converse is the established zero law for the real flow.")),
                    Paragraph(Text(
                        "The pinned library supplies the additive-circle zero criterion, the "
                            + "Archimedean natural bound, and the integer absolute-value lemma. "
                            + "The repository's coordinate formula assembles them into the "
                            + "universal-solenoid kernel criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-universal-solenoid-real-flow-is-injective"),
                DeclarationHandle.Create(
                    "D5/S1/Solenoid/RealFlowInjectivity.realFlow_injective"),
                H("The real flow is injective"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Injective")), Open,
                    F.Id("realFlow"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The existing real-flow additive homomorphism is injective exactly when "
                        + "its kernel is trivial. Applying the preceding kernel criterion "
                        + "therefore proves faithfulness of the real action."))),
                DescribeRole.Theorem))));
}
