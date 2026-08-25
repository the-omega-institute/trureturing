using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class ParetoWeakPreorderDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoWeakPreorder."
            + "pareto_weak_reflexive_transitive";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five independently preordered gain coordinates induce a preorder of actions.",
        H("Pareto Weak Dominance Preorder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pareto-weak-reflexive-transitive"),
                DeclarationHandle.Create(Declaration),
                H("Weak Pareto dominance is reflexive and transitive"),
                StatementSource.FromAuthor(ParetoPreorderFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Information, residual capture, and transfer are benefit coordinates; "
                            + "lifecycle cost and risk are burden coordinates. Weak dominance "
                            + "therefore reverses the comparison direction on the final two "
                            + "coordinates.")),
                    Paragraph(Text(
                        "Coordinate reflexivity proves self-dominance. Coordinate transitivity "
                            + "composes two dominance comparisons, independently in all five "
                            + "heterogeneous preorder types."))),
                DescribeRole.Theorem))));

    private static Formula Pareto(Formula value, Formula better, Formula worse) =>
        Call("ParetoWeak", value, better, worse);

    private static Formula ParetoPreorderFormula()
    {
        Formula action = F.Id("Action");
        Formula information = F.Id("Information");
        Formula residual = F.Id("Residual");
        Formula transfer = F.Id("Transfer");
        Formula cost = F.Id("Cost");
        Formula risk = F.Id("Risk");
        Formula value = F.Id("value");
        Formula first = F.Id("a");
        Formula second = F.Id("b");
        Formula third = F.Id("c");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula gainVector = Call(
            "GainVector", information, residual, transfer, cost, risk);
        Formula reflexive = Seq(
            Forall, Sp, first, Colon, Sp, action, Comma, Sp,
            Pareto(value, first, first));
        Formula transitive = Seq(
            Forall, Sp, first, Comma, Sp, second, Comma, Sp, third,
            Colon, Sp, action, Comma, Sp,
            Pareto(value, first, second), Sp, Rightarrow, Sp,
            Pareto(value, second, third), Sp, Rightarrow, Sp,
            Pareto(value, first, third));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, action, Comma, Sp, information, Comma, Sp,
            residual, Comma, Sp, transfer, Comma, Sp, cost, Comma, Sp, risk,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            Call("Preorder", information), Comma, Sp,
            Call("Preorder", residual), Comma, Sp,
            Call("Preorder", transfer), Comma, Sp,
            Call("Preorder", cost), Comma, Sp,
            Call("Preorder", risk), Comma, RowBreak, Grp(),
            value, Colon, Sp, action, Sp, To, Sp, gainVector, Comma, RowBreak, Grp(),
            Open, reflexive, Close, Sp, Land, RowBreak, Grp(),
            Open, transitive, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
