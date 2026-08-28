using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class TargetRelativeCommitmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One commitment can protect balance while exposing three other history targets.",
        H("Target-Relative Commitment Protection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("commitment-protection-is-target-relative"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Audits/TargetRelativeCommitment."
                        + "commitment_protection_is_target_relative"),
                H("Commitment protection must name its history target"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A history carries a mode bit followed by balance, event-order, "
                            + "identity-source, and contract-authorization coordinates.")),
                    Paragraph(Text(
                        "The unauthorized edit changes balance in the first mode and changes "
                            + "the other three targets in the second. The commitment stores the "
                            + "Boolean complement of balance, so its injectivity detects every "
                            + "balance change.")),
                    Paragraph(Text(
                        "At the second witness, the commitment and balance remain equal across "
                            + "the edit while order, identity source, and authorization all change "
                            + "on that same history. The negative clauses therefore cannot be "
                            + "separated into unrelated witnesses.")),
                    Paragraph(Text(
                        "The final public clause applies the same collision to the order target "
                            + "and rules out protection that is independent of the named target."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Tuple(params Formula[] entries)
    {
        var items = new List<Formula> { Open };
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(entries[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Assign(Formula left, Formula right) =>
        Seq(left, Sp, Colon, Eq, Sp, right);

    private static Formula TheoremFormula()
    {
        Formula historyType = F.Id("History");
        Formula boolean = F.Id("Bool");
        Formula mode = F.Id("m");
        Formula balanceValue = F.Id("b");
        Formula orderValue = F.Id("o");
        Formula originValue = F.Id("i");
        Formula authorizationValue = F.Id("a");
        Formula history = F.Id("gamma");
        Formula edit = F.Id("edit");
        Formula commitment = F.Id("commitment");
        Formula balance = F.Id("balance");
        Formula order = F.Id("eventOrder");
        Formula origin = F.Id("identitySource");
        Formula authorization = F.Id("contractAuthorization");
        Formula otherWitness = F.Id("otherEdit");
        Formula target = F.Id("T");
        Formula falseValue = F.Id("false");
        Formula coordinates = Tuple(
            mode, balanceValue, orderValue, originValue, authorizationValue);
        Formula changedBalance = Tuple(
            mode, Call("not", balanceValue), orderValue, originValue,
            authorizationValue);
        Formula changedOthers = Tuple(
            mode, balanceValue, Call("not", orderValue), Call("not", originValue),
            Call("not", authorizationValue));
        Formula editedHistory = Apply(edit, history);
        Formula collision = Seq(
            Apply(commitment, history), Sp, Eq, Sp,
            Apply(commitment, editedHistory));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Assign(
                historyType,
                Seq(boolean, Sp, Times, Sp, boolean, Sp, Times, Sp, boolean,
                    Sp, Times, Sp, boolean, Sp, Times, Sp, boolean)), Comma,
            RowBreak, Grp(),
            Assign(Apply(edit, coordinates), Call("if", mode, changedBalance, changedOthers)),
            Comma, RowBreak, Grp(),
            Assign(Apply(commitment, coordinates), Call("not", balanceValue)), Comma, Sp,
            Assign(Apply(balance, coordinates), balanceValue), Comma,
            RowBreak, Grp(),
            Assign(Apply(order, coordinates), orderValue), Comma, Sp,
            Assign(Apply(origin, coordinates), originValue), Comma, Sp,
            Assign(Apply(authorization, coordinates), authorizationValue), Comma,
            RowBreak, Grp(),
            Assign(otherWitness, Tuple(falseValue, falseValue, falseValue, falseValue, falseValue)),
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, history, InMacro, Sp, historyType, Comma, Sp,
            collision, Sp, Rightarrow, Sp,
            Apply(balance, history), Sp, Eq, Sp, Apply(balance, editedHistory), Close,
            Sp, Land, RowBreak, Grp(),
            Apply(commitment, otherWitness), Sp, Eq, Sp,
            Apply(commitment, Apply(edit, otherWitness)), Sp, Land,
            RowBreak, Grp(),
            Apply(order, otherWitness), Sp, Neq, Sp,
            Apply(order, Apply(edit, otherWitness)), Sp, Land,
            RowBreak, Grp(),
            Apply(origin, otherWitness), Sp, Neq, Sp,
            Apply(origin, Apply(edit, otherWitness)), Sp, Land,
            RowBreak, Grp(),
            Apply(authorization, otherWitness), Sp, Neq, Sp,
            Apply(authorization, Apply(edit, otherWitness)), Sp, Land,
            RowBreak, Grp(),
            Neg, Sp, Open,
            Forall, Sp, target, Colon, Sp,
            Seq(historyType, Sp, To, Sp, boolean), Comma, Sp,
            Forall, Sp, history, InMacro, Sp, historyType, Comma, Sp,
            collision, Sp, Rightarrow, Sp,
            Apply(target, history), Sp, Eq, Sp, Apply(target, editedHistory),
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
