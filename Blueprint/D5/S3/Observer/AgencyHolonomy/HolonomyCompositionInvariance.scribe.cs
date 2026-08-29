using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Holonomy;

internal sealed class HolonomyCompositionInvarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Agency/Holonomy/HolonomyCompositionInvariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Policy-invisible memory transports are closed under composition.",
        H("Holonomy Composition Invariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("invisible-transports-compose"),
                DeclarationHandle.Create(Prefix + "invisible_transports_compose"),
                H("Invisible transports compose"),
                StatementSource.FromAuthor(CompositionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume first and second each preserve the policy value at every memory "
                            + "state.")),
                    Paragraph(Text(
                        "Apply second's invariance after first, then first's invariance. Their "
                            + "composite is therefore policy-invisible at every memory."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("identity-transport-is-invisible"),
                DeclarationHandle.Create(Prefix + "identity_transport_invisible"),
                H("Identity transport is invisible"),
                StatementSource.FromAuthor(IdentityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The identity memory transport leaves every memory state unchanged.")),
                    Paragraph(Text(
                        "It is consequently policy-invisible for every policy, without any "
                            + "additional hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula CompositionStatement()
    {
        Formula policy = F.Id("policy");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula antecedent = Seq(
            Call("PolicyInvisible", policy, first), Sp, Land, Sp,
            Call("PolicyInvisible", policy, second));
        return Disp(Seq(
            Forall, Sp, policy, Colon, Sp, Arrow(F.Id("M"), F.Id("A")), Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, Arrow(F.Id("M"), F.Id("M")),
            Comma, RowBreak, Grp(),
            Open, antecedent, Close, Sp, Rightarrow, Sp,
            Call("PolicyInvisible", policy, Seq(second, Sp, Circ, Sp, first)), Dot));
    }

    private static Formula IdentityStatement()
    {
        Formula policy = F.Id("policy");
        return Disp(Seq(
            Forall, Sp, policy, Colon, Sp, Arrow(F.Id("M"), F.Id("A")), Comma, Sp,
            Call("PolicyInvisible", policy, F.Id("id")), Dot));
    }
}
