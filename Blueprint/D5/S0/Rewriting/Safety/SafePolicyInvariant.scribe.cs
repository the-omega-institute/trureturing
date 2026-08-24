using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Safety;

internal sealed class SafePolicyInvariantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula state = F.Id("x");
        Formula next = F.Id("y");
        Formula control = F.Id("u");
        Formula initial = new Formula.Subscript(F.Id("x"), D(0));
        Formula current = new Formula.Subscript(F.Id("x"), F.Id("t"));
        Formula kernel = Seq(F.Id("K"), Caret, Star);
        Formula safe = F.Id("S");
        Formula policy = F.Id("pi");
        Formula availableAtState = Seq(F.Id("U"), Open, state, Close);
        Formula response = Call("R", state, control, next);
        Formula safeControls = Seq(F.Id("U"), Underscore, Grp(F.Id("safe")));
        Formula policyStep = Call("PolicyStep", F.Id("R"), policy);
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            kernel, Sp, Subseteq, Sp, safe, Comma, RowBreak, Grp(),
            safeControls, Open, state, Close, Sp, Colon, Eq, Sp,
            OpenBrace, control, Sp, InMacro, Sp, availableAtState, Sp, Mid, Sp,
            Forall, Sp, next, Comma, Sp, response, Sp, Rightarrow, Sp,
            next, Sp, InMacro, Sp, kernel, CloseBrace, Comma, RowBreak, Grp(),
            Forall, Sp, state, Comma, Sp,
            policy, Open, state, Close, Sp, InMacro, Sp,
            safeControls, Open, state, Close, RowBreak, Grp(),
            Rightarrow, Sp, Forall, Sp, initial, Comma, Sp, current, Comma, Sp,
            initial, Sp, InMacro, Sp, kernel, Sp, Land, Sp,
            Call("Reachable", policyStep, initial, current), RowBreak, Grp(),
            Rightarrow, Sp, current, Sp, InMacro, Sp, kernel, Sp, Land, Sp,
            current, Sp, InMacro, Sp, safe, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A policy selecting only controls whose possible responses stay in the safe kernel preserves the kernel and safety.",
            H("Safe Policy Invariance"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("safe-policy-preserves-kernel"),
                    DeclarationHandle.Create(
                        "D5/S0/Rewriting/Safety/SafePolicyInvariant."
                            + "safe_policy_preserves_kernel"),
                    H("Safe policies preserve the safe kernel"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For each state, the safe-control set is constructed from the "
                                + "available controls and the response relation: every possible "
                                + "successor must lie in the safe kernel.")),
                        Paragraph(Text(
                            "The policy-induced transition relation is passed directly to the "
                                + "canonical invariant-safety theorem. Every finitely reachable "
                                + "state therefore lies in the kernel and, by inclusion, in S."))),
                    DescribeRole.Theorem))));
    }
}
