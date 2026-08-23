using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class FiniteHorizonOptimalActionDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact causal abstraction preserves every finite-horizon optimal-action set.",
        H("Finite-Horizon Optimal-Action Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-horizon-optimal-actions-descend"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent."
                        + "finite_horizon_optimal_actions_descend"),
                H("Optimal action concept descends"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, F.Id("U"), Close,
                    CloseBracket, Comma, Sp, F.Id("U"), Sp, Neq, Sp, Emptyset, Comma,
                    RowBreak, Grp(),
                    Open, Forall, Sp, F.Id("u"), Comma, Sp, F.Id("x"), Comma, Sp,
                    F.Id("C"), Open, F.Id("F"), Underscore, Grp(F.Id("u")),
                    Open, F.Id("x"), Close, Close, Sp, Eq, Sp,
                    F.Id("G"), Underscore, Grp(F.Id("u")), Open, F.Id("C"),
                    Open, F.Id("x"), Close, Close, Close, Sp, Land, RowBreak, Grp(),
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("u"), Comma, Sp,
                    F.Id("r"), Open, F.Id("x"), Comma, Sp, F.Id("u"), Close,
                    Sp, Eq, Sp, Overline, Grp(F.Id("r")), Open, F.Id("C"),
                    Open, F.Id("x"), Close, Comma, Sp, F.Id("u"), Close, Close,
                    Sp, Land, RowBreak, Grp(),
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    F.Id("q"), Open, F.Id("x"), Close, Sp, Eq, Sp,
                    Overline, Grp(F.Id("q")), Open, F.Id("C"), Open, F.Id("x"),
                    Close, Close, Close, Longrightarrow, RowBreak, Grp(),
                    Forall, Sp, F.Id("n"), Comma, Sp, F.Id("x"), Comma, Sp,
                    Operatorname, Grp(F.Id("argmax")), Underscore,
                    Grp(Seq(F.Id("u"), InMacro, Sp, F.Id("U"))), Sp,
                    OpenBracket, F.Id("r"), Open, F.Id("x"), Comma, Sp, F.Id("u"),
                    Close, Sp, Plus, Sp, F.Id("V"), Underscore, Grp(F.Id("n")),
                    Open, F.Id("F"), Underscore, Grp(F.Id("u")), Open, F.Id("x"),
                    Close, Close, CloseBracket, Sp, Eq, RowBreak, Grp(),
                    Operatorname, Grp(F.Id("argmax")), Underscore,
                    Grp(Seq(F.Id("u"), InMacro, Sp, F.Id("U"))), Sp,
                    OpenBracket, Overline, Grp(F.Id("r")), Open, F.Id("C"),
                    Open, F.Id("x"), Close, Comma, Sp, F.Id("u"), Close, Sp, Plus, Sp,
                    Overline, Grp(Seq(F.Id("V"), Underscore, Grp(F.Id("n")))),
                    Open, F.Id("G"), Underscore, Grp(F.Id("u")), Open, F.Id("C"),
                    Open, F.Id("x"), Close, Close, Close, CloseBracket, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The common action carrier is finite and nonempty. Micro transitions "
                            + "commute with the abstraction, while both stage rewards and terminal "
                            + "values factor through the abstract state.")),
                    Paragraph(Text(
                        "Induction through the finite maximum first identifies the micro Bellman "
                            + "value with the macro value at C(x). Substitution in each action "
                            + "score "
                            + "then identifies the two maximizing-action sets pointwise, so the "
                            + "optimal decision depends only on C(x)."))),
                DescribeRole.Theorem))));
}
