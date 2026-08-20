using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class PrecedentTargetCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Target completion preserves old cases but need not supply an independent permitted reason.",
        H("Target Completion and Noncircular Distinction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("target-completion-formal-but-not-noncircular"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/PrecedentTargetCompletion."
                        + "target_completion_formal_distinction_not_noncircular"),
                H("Formal target completion does not supply a noncircular reason"),
                StatementSource.FromAuthor(StatementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary case states, old facts, and verdicts, agreement on the old "
                            + "case set yields a decision through the canonical join of the old "
                            + "facts with the new verdict. The resulting decision still agrees with "
                            + "the old verdict on every old case.")),
                    Paragraph(Text(
                        "The public countermodel uses Boolean cases. The permitted doctrine is "
                            + "nonempty and every permitted fact has the same value on the two "
                            + "cases, so it is specified without consulting the target verdict.")),
                    Paragraph(Text(
                        "The target-completed interface decides the identity verdict, while no "
                            + "permitted fact joined with the constant old fact can do so. The final "
                            + "public conjunct is the resulting failure of the implication from "
                            + "formal distinction to a permitted noncircular reason.")),
                    Paragraph(Text(
                        "The formal-completion clause directly applies the repository theorem "
                            + "`concept_join_universal`; repository and pinned-library searches found "
                            + "no theorem packaging it with old-case preservation and the doctrine "
                            + "countermodel."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Compose(Formula left, Formula right) =>
        Seq(left, Sp, Circ, Sp, right);

    private static Formula Join(Formula first, Formula second) =>
        Call("conceptJoin", first, second);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula EqOn(Formula first, Formula second, Formula domain) =>
        Call("EqOn", first, second, domain);

    private static Formula StatementFormula()
    {
        Formula state = F.Id("X");
        Formula factType = F.Id("C");
        Formula verdict = F.Id("Y");
        Formula oldCases = F.Id("A");
        Formula oldFact = F.Id("q");
        Formula oldDecision = Subscript(F.Id("J"), D(0));
        Formula newDecision = Subscript(F.Id("J"), D(1));
        Formula decide = F.Id("d");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula join = Join(oldFact, newDecision);
        Formula completion = Seq(
            Exists, Sp, decide, Colon, Sp,
            Arrow(Seq(factType, Sp, Times, Sp, verdict), verdict), Comma, Sp,
            newDecision, Sp, Eq, Sp, Compose(decide, join), Sp, Land, Sp,
            EqOn(Compose(decide, join), oldDecision, oldCases));
        Formula generalClause = Seq(
            Forall, Sp, state, Comma, Sp, factType, Comma, Sp, verdict,
            Colon, Sp, type, Comma, Esc,
            oldCases, Colon, Sp, Call("Set", state), Comma, Sp,
            oldFact, Colon, Sp, Arrow(state, factType), Comma, Sp,
            oldDecision, Comma, Sp, newDecision, Colon, Sp,
            Arrow(state, verdict), Comma, Esc,
            EqOn(newDecision, oldDecision, oldCases), Sp, Rightarrow, Sp,
            completion);

        Formula boolean = F.Id("Bool");
        Formula b = F.Id("b");
        Formula falseValue = F.Id("false");
        Formula trueValue = F.Id("true");
        Formula identity = F.Id("id");
        Formula constant = Seq(
            Open, LambdaLower, Sp, b, Colon, Sp, boolean, Comma, Sp,
            falseValue, Close);
        Formula doctrine = F.Id("E");
        Formula fact = F.Id("D");
        Formula singletonFalse = Seq(OpenBrace, falseValue, CloseBrace);
        Formula boolReadout = Arrow(boolean, boolean);
        Formula counterJoin = Join(constant, identity);
        Formula counterCompletion = Seq(
            Exists, Sp, decide, Colon, Sp,
            Arrow(Seq(boolean, Sp, Times, Sp, boolean), boolean), Comma, Sp,
            identity, Sp, Eq, Sp, Compose(decide, counterJoin), Sp, Land, Sp,
            EqOn(Compose(decide, counterJoin), constant, singletonFalse));
        Formula legalReason = Seq(
            Exists, Sp, fact, Colon, Sp, boolReadout, Comma, Sp,
            fact, Sp, InMacro, Sp, doctrine, Sp, Land, Sp,
            Refines(identity, Join(constant, fact)));
        Formula formalDistinction = Seq(
            EqOn(identity, constant, singletonFalse), Sp, Land, Sp,
            counterCompletion);
        Formula targetIndependent = Seq(
            Forall, Sp, fact, Colon, Sp, boolReadout, Comma, Sp,
            fact, Sp, InMacro, Sp, doctrine, Sp, Rightarrow, Sp,
            Apply(fact, falseValue), Sp, Eq, Sp, Apply(fact, trueValue));
        Formula countermodel = Seq(
            Exists, Sp, doctrine, Colon, Sp, Call("Set", boolReadout), Comma, Esc,
            constant, Sp, InMacro, Sp, doctrine, Sp, Land, Sp,
            Open, targetIndependent, Close, Sp, Land, Sp,
            EqOn(identity, constant, singletonFalse), Sp, Land, Sp,
            Open, counterCompletion, Close, Sp, Land, Esc,
            Open, Neg, Sp, Open, legalReason, Close, Close, Sp, Land, Sp,
            Neg, Sp, Open, Open, formalDistinction, Close, Sp,
            Rightarrow, Sp, legalReason, Close);

        return Disp(Seq(
            Open, generalClause, Close, Sp, Land, Esc,
            Open, countermodel, Close, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
