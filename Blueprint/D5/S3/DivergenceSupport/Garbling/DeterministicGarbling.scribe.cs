using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport.Garbling;

internal sealed class DeterministicGarblingDocument : IScribeDocumentDefinition
{
    private static Formula Pushforward(Formula law) =>
        F.Seq(F.Id("f"), F.Underscore, F.Grp(F.Star), law);

    private static Formula Divergence(Formula left, Formula right) =>
        F.Seq(F.Id("D"), F.Open, left, F.Vert, F.Vert, F.Sp, right, F.Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic finite forgetting has nonnegative Kullback-Leibler information loss.",
        H("Kullback-Leibler Loss under Deterministic Forgetting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("deterministic-forgetting-has-nonnegative-kl-loss"),
                DeclarationHandle.Create(
                    "D5/S3/DivergenceSupport/Garbling/DeterministicGarbling."
                        + "deterministic_forgetting_kl_loss_nonnegative"),
                H("Deterministic forgetting has nonnegative KL loss"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Y"), Esc,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")),
                    Open, F.Id("X"), Close, CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")),
                    Open, F.Id("Y"), Close, CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    F.Id("X"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("f"), Colon, Sp, F.Id("X"), To, Sp, F.Id("Y"), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp, Sum, Underscore, Grp(F.Id("x")),
                    F.Id("p"), Open, F.Id("x"), Close, Eq, D(1), Close,
                    Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp, Sum, Underscore, Grp(F.Id("x")),
                    F.Id("q"), Open, F.Id("x"), Close, Eq, D(1), Close,
                    Sp, Rightarrow, RowBreak,
                    Open, Forall, Sp, F.Id("x"), Colon, Sp, F.Id("X"), Comma, Sp,
                    F.Id("q"), Open, F.Id("x"), Close, Eq, D(0), Sp,
                    Rightarrow, Sp, F.Id("p"), Open, F.Id("x"), Close, Eq, D(0), Close,
                    Sp, Rightarrow, RowBreak,
                    Divergence(F.Id("p"), F.Id("q")), Sp, Minus, Sp,
                    Divergence(Pushforward(F.Id("p")), Pushforward(F.Id("q"))),
                    Sp, Ge, Sp, D(0), Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite types, let p and q be nonnegative normalized "
                            + "mass functions on X, and assume discrete absolute continuity: "
                            + "every zero of q is also a zero of p. A function f : X -> Y "
                            + "forgets distinctions inside its fibers; f_*p and f_*q are the "
                            + "resulting pushforward laws.")),
                    Paragraph(Text(
                        "The graph of f defines a zero-one channel with nonnegative entries and "
                            + "unit row sums. Applying the frozen general-support data-processing "
                            + "defect theorem to that channel proves the displayed inequality. "
                            + "The only local argument identifies its channel outputs with the "
                            + "deterministic pushforwards."))),
                DescribeRole.Theorem)
        )));
}
