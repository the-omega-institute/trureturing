using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.EscapeProbability;

internal sealed class PoissonDomainLimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite scaled fixed-point weight gives the exponential limit of the frozen escape probability.",
        H("Poisson-Domain Escape Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("poisson-domain-escape-limit"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/EscapeProbability/PoissonDomainLimit."
                        + "poisson_domain_escape_probability_limit"),
                H("Scaled fixed points give the Poisson-domain escape-probability limit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("Y"),
                    CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, F.Id("Y"),
                    CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Y"), Sp, To, Sp, F.Id("Y"),
                    Comma, Sp,
                    LambdaLower, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Left, Open,
                    Lim, Underscore, Grp(F.Id("A"), Sp, To, Sp, Infty), Sp,
                    Call("card", Call("Fix", F.Id("f"))), Sp, F.Id("A"), Sp,
                    Call("card", F.Id("Y")),
                    Caret, Grp(Minus, F.Id("A")), Sp, Eq, Sp, LambdaLower,
                    Right, Close, Sp, Rightarrow, Sp,
                    Lim, Underscore, Grp(F.Id("A"), Sp, To, Sp, Infty), Sp,
                    Call("escapeProbability", Call("Fin", F.Id("A")), F.Id("f")),
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("exp")),
                    Open, Minus, LambdaLower, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite nonempty output type Y and f:Y->Y, put n=|Y| and "
                            + "k=|Fix(f)|. If the real scaled weight k A n^(-A) tends to "
                            + "lambda, then the repository's frozen escape probability on "
                            + "Fin A tends to exp(-lambda).")),
                    Paragraph(Text(
                        "The public closed-form lemma derives P_esc(Fin A,f)="
                            + "(1-k/n^A)^A from escaped_listing_card and the Nat.card ratio "
                            + "definition. The supporting analytic theorem then applies pinned "
                            + "Mathlib's Real.tendsto_one_add_pow_exp_of_tendsto.")),
                    Paragraph(Text(
                        "This is the analytic conditional from the older Poisson-domain clause. "
                            + "The current corrected model clause is compatible with it: when "
                            + "k(A) is an actual fixed-point count bounded by n(A) in the fixed "
                            + "n at least two regime, the scaled weight tends to zero, so no "
                            + "positive Poisson parameter is realizable."))),
                DescribeRole.Theorem)),
        []));
}
