using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics;

internal sealed class EscapeProbabilityMonotoneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Escape probability is nondecreasing in guarded address cardinality and has the one-address value.",
        H("Escape Probability Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("escape-probability-monotone-and-one-address"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/EscapeProbabilityMonotone.escape_probability_monotone_and_one_address"),
                H("Escape probability is monotone and has the one-address value"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("Y"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("Y"), CloseBracket, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("Nonempty")), Sp, F.Id("Y"), CloseBracket, Comma, Sp,
                    Forall, Sp, F.Id("f"), Colon, Sp, F.Id("Y"), To, Sp, F.Id("Y"), Comma, Sp,
                    Open, Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), InMacro,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("a"), Sp, Ge, Sp, D(1), Sp, Land, Sp,
                    F.Id("b"), Sp, Ge, Sp, D(1), Sp, Land, Sp,
                    F.Id("a"), Sp, Le, Sp, F.Id("b"), Sp, Rightarrow, Sp,
                    Call("escapeProbability", Call("Fin", F.Id("a")), F.Id("f")), Sp, Le, Sp,
                    Call("escapeProbability", Call("Fin", F.Id("b")), F.Id("f")), Close, Sp, Land, Sp,
                    Call("escapeProbability", Call("Fin", D(1)), F.Id("f")), Sp, Eq, Sp,
                    D(1), Sp, Minus, Sp,
                    Frac, Grp(Call("card", Call("Fix", F.Id("f")))),
                    Grp(Call("card", F.Id("Y"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite nonempty value type Y, the exact "
                        + "escape probability is nondecreasing as the guarded address cardinality "
                        + "increases. At address cardinality one it equals one minus the fixed-point "
                        + "count divided by the value cardinality.")),
                    Paragraph(Text(
                        "The proof first rewrites the repository's escapeProbability definition using "
                        + "the frozen escaped_listing_card count. The successor inequality is then "
                        + "an elementary Bernoulli bound for the exact formula "
                        + "((n^A-k)/n^A)^A; the finite fixed-point subtype supplies k <= n.")),
                    Paragraph(Text(
                        "The source clause is guarded by 1 <= A. At A = 0 the formula evaluates to "
                        + "P_esc(0) = 1, while for k > 0 it gives P_esc(1) = 1 - k/n < 1; "
                        + "therefore unguarded monotonicity is false and the A = 1 endpoint must be "
                        + "stated on the guarded domain to faithfully express the paper's escape-rate "
                        + "claim. This deposit closes only clause (ii); source clause (v) remains "
                        + "unformalized, so corollary 3.6 is not fully closed."))),
                DescribeRole.Theorem)),
        []));
}
