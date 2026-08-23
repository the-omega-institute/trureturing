using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Appeal;

internal sealed class ExplainableNotContestableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A public rule can remain explainable while case and appeal evidence cannot determine "
            + "its outcome.",
        H("Explainable but Not Contestable"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("explainable-not-contestable"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Appeal/ExplainableNotContestable."
                        + "explainable_not_contestable"),
                H("A public rule need not make its outcome contestable"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take the state space to be two Boolean coordinates. The rule, its "
                            + "public language, and the case record all reveal the first "
                            + "coordinate, so the rule is fully explainable through the public "
                            + "language.")),
                    Paragraph(Text(
                        "The appeal readout is constant and therefore contributes no new "
                            + "distinction. The classification target is the second coordinate, "
                            + "which the joined case-and-appeal evidence does not reveal.")),
                    Paragraph(Text(
                        "In particular, the states (false, false) and (false, true) have the "
                            + "same case record and the same appeal evidence, but their target "
                            + "outcomes differ. Hence no function of the available joined "
                            + "evidence can recover the canonical target readout.")),
                    Paragraph(Text(
                        "This finite witness separates publication of the governing rule from "
                            + "contestability of an individual outcome: knowing the rule does "
                            + "not supply the case-specific coordinate needed to challenge the "
                            + "classification."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula boolType = F.Id("Bool");
        Formula state = Seq(boolType, Sp, Times, Sp, boolType);
        Formula readoutType = Seq(state, Sp, To, Sp, boolType);
        Formula rule = Subscript(F.Id("q"), F.Id("R"));
        Formula language = Subscript(F.Id("q"), F.Id("L"));
        Formula caseReadout = Subscript(F.Id("q"), F.Id("C"));
        Formula appeal = Subscript(F.Id("q"), F.Id("A"));
        Formula target = F.Id("T");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula joined = Call("conceptJoin", caseReadout, appeal);
        Formula canonicalTarget = Call("canonicalTargetReadout", target);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp,
            Typed(
                Seq(rule, Comma, Sp, language, Comma, Sp, caseReadout, Comma, Sp, appeal),
                readoutType),
            Comma, Sp, Typed(target, readoutType), Comma, RowBreak, Grp(),
            Call("Refines", rule, language), Sp, Land, Sp,
            Open, Forall, Sp, Typed(Seq(x, Comma, Sp, y), state), Comma, Sp,
            Apply(appeal, x), Sp, Eq, Sp, Apply(appeal, y), Close, Sp, Land, RowBreak,
            Grp(),
            Neg, Sp, Call("Refines", canonicalTarget, joined), Sp, Land, RowBreak, Grp(),
            Exists, Sp, Typed(Seq(x, Comma, Sp, y), state), Comma, Sp,
            Apply(target, x), Sp, Neq, Sp, Apply(target, y), Sp, Land, Sp,
            Apply(joined, x), Sp, Eq, Sp, Apply(joined, y), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
