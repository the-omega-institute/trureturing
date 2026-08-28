using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class PosteriorApprovalAuthorizationGapDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/NormativeStructure/PosteriorApprovalAuthorizationGap."
            + "posterior_approval_does_not_imply_prior_authorization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A change can produce the approval standard under which it is later accepted.",
        H("Posterior Approval Does Not Establish Prior Authorization"),
        Blocks(Describe.Lean(
            DescribeId.Create(
                "posterior-approval-does-not-imply-prior-authorization"),
            DeclarationHandle.Create(Declaration),
            H("Posterior approval can coexist with prior nonauthorization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A subject state consists of an action-preference bit and an approval-"
                        + "standard bit. The displayed process negates both components, so the "
                        + "model records both changes publicly.")),
                Paragraph(Text(
                    "A state authorizes a process exactly when its approval bit is true and the "
                        + "process changes that state. Starting from two false bits, the original "
                        + "state does not authorize the process, while the resulting state does.")),
                Paragraph(Text(
                    "The final public clause exhibits the failed implication from posterior "
                        + "approval to prior authorization. The process and authorization rule "
                        + "are constructed independently of that failed implication."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula boolType = F.Id("Bool");
        Formula stateType = Seq(boolType, Sp, Times, Sp, boolType);
        Formula state = F.Id("y");
        Formula process = F.Id("P");
        Formula preference = F.Id("A");
        Formula standard = F.Id("R");
        Formula change = F.Id("G");
        Formula original = F.Id("x");
        Formula trueValue = Seq(Operatorname, Grp(F.Id("true")));
        Formula falseValue = Seq(Operatorname, Grp(F.Id("false")));
        Formula changedOriginal = Apply(change, original);
        Formula priorAuthorization = Subscript(Call("Auth", change), original);
        Formula posteriorAuthorization =
            Subscript(Call("Auth", change), changedOriginal);

        Formula sourceObjects = Seq(
            preference, Colon, Sp, stateType, Sp, To, Sp, boolType, Comma, Sp,
            Apply(preference, Pair(F.Id("a"), F.Id("r"))), Sp, Eq, Sp, F.Id("a"),
            Comma, RowBreak, Grp(),
            standard, Colon, Sp, stateType, Sp, To, Sp, boolType, Comma, Sp,
            Apply(standard, Pair(F.Id("a"), F.Id("r"))), Sp, Eq, Sp, F.Id("r"),
            Comma, RowBreak, Grp(),
            Apply(change, Pair(F.Id("a"), F.Id("r"))), Sp, Eq, Sp,
            Pair(Seq(Neg, Sp, Apply(preference, Pair(F.Id("a"), F.Id("r")))),
                Seq(Neg, Sp, Apply(standard, Pair(F.Id("a"), F.Id("r"))))),
            Comma, RowBreak, Grp(),
            Forall, Sp, state, Colon, Sp, stateType, Comma, Sp,
            process, Colon, Sp, stateType, Sp, To, Sp, stateType, Comma, Sp,
            Subscript(Call("Auth", process), state), Sp, Leftrightarrow, Sp,
            Open, Apply(standard, state), Sp, Eq, Sp, trueValue, Sp, Land, Sp,
            Apply(process, state), Sp, Neq, Sp, state, Close,
            Comma, RowBreak, Grp(),
            original, Sp, Eq, Sp, Pair(falseValue, falseValue));

        Formula conclusion = Seq(
            Apply(preference, changedOriginal), Sp, Neq, Sp,
            Apply(preference, original), Sp, Land, RowBreak, Grp(),
            Apply(standard, changedOriginal), Sp, Neq, Sp,
            Apply(standard, original), Sp, Land, RowBreak, Grp(),
            Neg, Sp, priorAuthorization, Sp, Land, Sp,
            posteriorAuthorization, Sp, Land, RowBreak, Grp(),
            Neg, Open, posteriorAuthorization, Sp, Rightarrow, Sp,
            priorAuthorization, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            sourceObjects, Colon, RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
