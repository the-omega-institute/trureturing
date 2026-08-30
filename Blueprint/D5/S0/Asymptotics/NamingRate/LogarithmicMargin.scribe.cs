using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.NamingRate;

internal sealed class LogarithmicMarginDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var natural = F.Id("N");
        var real = F.Id("R");
        var error = F.Id("error");
        var n0 = new Formula.Subscript(F.Id("n"), D(0));
        var n = F.Id("n");
        var realN = Call("castReal", n);
        var logarithmic = Call(
            "lambda",
            Call("typed", n, natural),
            Call("log", realN));
        var bigO = Call("IsBigO", error, F.Id("atTop"), logarithmic);
        var margin = Seq(
            Frac, Grp(realN), Grp(D(2)), Sp, Minus, Sp, Apply(error, n),
            Sp, Gt, Sp, Frac, Grp(realN), Grp(D(4)));
        var conclusion = Seq(
            Exists, Sp, Typed(n0, natural), Comma, Sp,
            Forall, Sp, Typed(n, natural), Comma, Sp,
            n, Sp, Ge, Sp, n0, Sp, Rightarrow, Sp, margin);

        return DocumentDefinition.Create(ScribeNode.Create(
            "A logarithmic error eventually leaves a strict quarter-scale linear margin.",
            H("Logarithmic Error Leaves a Linear Margin"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("a-logarithmic-error-eventually-leaves-a-quarter-scale-margin"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/NamingRate/LogarithmicMargin." +
                        "logarithmic_error_eventually_leaves_quarter_margin"),
                    H("The logarithmic remainder is eventually below the linear gap"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, Typed(error, Seq(natural, Sp, To, Sp, real)), Comma, Sp,
                        bigO, Sp, Rightarrow, Sp, conclusion, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let error be any real-valued sequence on the natural numbers. If it " +
                            "is bounded by a constant multiple of log n at infinity, then from " +
                            "some index onward n / 2 - error(n) is strictly greater than n / 4.")),
                        Paragraph(Text(
                            "Pinned Mathlib supplies Real.isLittleO_log_id_atTop. The proof " +
                            "restricts this real asymptotic to natural inputs, composes it with " +
                            "the stated big-O premise, and takes an explicit one-eighth bound.")),
                        Paragraph(Text(
                            "This deposit formalizes exactly theorem 4.5 clause 3: the logarithmic " +
                            "remainder is eventually dominated by the quarter-scale linear margin. " +
                            "The neighboring fast-witness and short-witness clauses are separate " +
                            "ledger atoms and are not restated here."))),
                    DescribeRole.Theorem)),
            []));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
}
