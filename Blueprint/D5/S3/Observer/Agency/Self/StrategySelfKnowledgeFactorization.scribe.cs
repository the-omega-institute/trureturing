using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Self;

internal sealed class StrategySelfKnowledgeFactorizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Agency/Self/StrategySelfKnowledgeFactorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strategy self-knowledge factorization refines the current-state observation kernel.",
        H("Strategy Self Knowledge Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factorization-refines-the-strategy-kernel"),
                DeclarationHandle.Create(Prefix + "factorization_refines_strategy_kernel"),
                H("Factorization refines the strategy kernel"),
                StatementSource.FromAuthor(ProfileStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume the strategy profile factors pointwise through the current-memory "
                            + "readout, and fix histories with equal current values.")),
                    Paragraph(Text(
                        "Substituting the factorization on both histories transports current "
                            + "equality to equality of their strategy profiles."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-visible-profile-adds-no-pairwise-separation"),
                DeclarationHandle.Create(Prefix + "visible_profile_pair_equality"),
                H("A visible profile adds no pairwise separation"),
                StatementSource.FromAuthor(PairStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same factorization and current-equality hypotheses, both the "
                            + "current and profile components agree.")),
                    Paragraph(Text(
                        "The paired agency-completion values are therefore equal for the displayed "
                            + "histories; no global kernel equality is asserted."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula PrefixFormula(Formula conclusion)
    {
        Formula h = F.Id("h");
        Formula factors = Seq(
            Forall, Sp, h, Colon, Sp, F.Id("H"), Comma, Sp,
            Call("profile", h), Sp, Eq, Sp,
            Call("factor", Call("current", h)));
        Formula sameCurrent = Seq(
            Call("current", F.Id("x")), Sp, Eq, Sp,
            Call("current", F.Id("y")));
        Formula antecedent = Seq(Open, factors, Close, Sp, Land, Sp, sameCurrent);
        return Disp(Seq(
            Forall, Sp, F.Id("current"), Colon, Sp,
            Arrow(F.Id("H"), F.Id("M")), Comma, Sp,
            F.Id("profile"), Colon, Sp, Arrow(F.Id("H"), F.Id("P")), Comma, Sp,
            F.Id("factor"), Colon, Sp, Arrow(F.Id("M"), F.Id("P")), Comma,
            RowBreak, Grp(),
            F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp, F.Id("H"), Comma, Sp,
            Open, antecedent, Close, Sp, Rightarrow, Sp, conclusion, Dot));
    }

    private static Formula ProfileStatement() => PrefixFormula(Seq(
        Call("profile", F.Id("x")), Sp, Eq, Sp, Call("profile", F.Id("y"))));

    private static Formula PairStatement()
    {
        Formula left = Call("pair", Call("current", F.Id("x")),
            Call("profile", F.Id("x")));
        Formula right = Call("pair", Call("current", F.Id("y")),
            Call("profile", F.Id("y")));
        return PrefixFormula(Seq(left, Sp, Eq, Sp, right));
    }
}
