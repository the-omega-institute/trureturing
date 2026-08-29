using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class ActionLoopRequiresMemoryDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/AgencyHolonomy/ActionLoopRequiresMemory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A policy-visible loop effect requires nontrivial memory transport.",
        H("Action Loop Requires Memory"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("policy-change-implies-memory-change"),
                DeclarationHandle.Create(Prefix + "policy_change_implies_memory_change"),
                H("Policy change implies memory change"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a question, memory state, memory transport, and policy. Assume the "
                            + "transport changes the policy's selected action.")),
                    Paragraph(Text(
                        "If the transported memory were unchanged, the two policy evaluations "
                            + "would coincide. The visible action change therefore forces a "
                            + "memory change."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("an-injective-policy-detects-memory-change"),
                DeclarationHandle.Create(Prefix + "injective_policy_detects_memory_change"),
                H("An injective policy coordinate detects memory change"),
                StatementSource.FromAuthor(DetectionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the converse direction, assume the policy at the chosen question is "
                            + "injective as a function of memory.")),
                    Paragraph(Text(
                        "A nontrivial memory transport must then change the selected action at "
                            + "that memory state. No injectivity is assumed at other questions."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula PrefixFormula(Formula antecedent, Formula conclusion) =>
        Disp(Seq(
            Forall, Sp, F.Id("policy"), Colon, Sp,
            Arrow(F.Id("Q"), Arrow(F.Id("M"), F.Id("A"))), Comma, Sp,
            F.Id("q"), Colon, Sp, F.Id("Q"), Comma, Sp,
            F.Id("h"), Colon, Sp, Arrow(F.Id("M"), F.Id("M")), Comma, Sp,
            F.Id("m"), Colon, Sp, F.Id("M"), Comma, RowBreak, Grp(),
            antecedent, Sp, Rightarrow, Sp, conclusion, Dot));

    private static Formula PolicyAt(Formula memory) =>
        Call("policy", F.Id("q"), memory);


    private static Formula DetectionStatement()
    {
        Formula transported = Call("h", F.Id("m"));
        Formula antecedent = Seq(
            Call("Injective", Call("policy", F.Id("q"))), Sp, Land, Sp,
            transported, Sp, Neq, Sp, F.Id("m"));
        Formula conclusion = Seq(
            PolicyAt(transported), Sp, Neq, Sp, PolicyAt(F.Id("m")));
        return PrefixFormula(Seq(Open, antecedent, Close), conclusion);
    }
}
