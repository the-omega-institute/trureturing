using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Agency.Holonomy;

internal sealed class HolonomyPolicyRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Agency/Holonomy/HolonomyPolicyRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An injective policy invariant under holonomy forces trivial holonomy.",
        H("Holonomy Policy Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("an-injective-invariant-policy-forces-identity-holonomy"),
                DeclarationHandle.Create(Prefix + "policy_invariant_holonomy_eq_identity"),
                H("An injective invariant policy forces identity holonomy"),
                StatementSource.FromAuthor(IdentityStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume a policy is injective in memory and invariant under a memory "
                            + "holonomy at every state.")),
                    Paragraph(Text(
                        "Injectivity reflects each invariant policy equality to a fixed-point "
                            + "equality. Extensionality makes the holonomy the identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-nontrivial-invisible-loop-remains-at-any-state"),
                DeclarationHandle.Create(Prefix + "no_nontrivial_invisible_loop"),
                H("No nontrivial invisible loop remains at any state"),
                StatementSource.FromAuthor(PointwiseStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same injectivity and pointwise invariance assumptions, fix one "
                            + "memory state.")),
                    Paragraph(Text(
                        "The policy equality at that state forces the transported memory to equal "
                            + "the original memory. The claim is pointwise, not a new converse."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Invariance()
    {
        Formula memory = F.Id("m");
        return Seq(
            Forall, Sp, memory, Colon, Sp, F.Id("M"), Comma, Sp,
            Call("policy", Call("h", memory)), Sp, Eq, Sp, Call("policy", memory));
    }

    private static Formula PrefixFormula(Formula conclusion, bool includeMemory)
    {
        Formula policy = F.Id("policy");
        Formula holonomy = F.Id("h");
        Formula antecedent = Seq(
            Call("Injective", policy), Sp, Land, Sp, Open, Invariance(), Close);
        Formula memoryBinder = includeMemory
            ? Seq(F.Id("m"), Colon, Sp, F.Id("M"), Comma, Sp)
            : Seq();
        return Disp(Seq(
            Forall, Sp, policy, Colon, Sp, Arrow(F.Id("M"), F.Id("A")), Comma, Sp,
            holonomy, Colon, Sp, Arrow(F.Id("M"), F.Id("M")), Comma, Sp,
            memoryBinder,
            Open, antecedent, Close, Sp, Rightarrow, Sp, conclusion, Dot));
    }

    private static Formula IdentityStatement() =>
        PrefixFormula(Seq(F.Id("h"), Sp, Eq, Sp, F.Id("id")), false);

    private static Formula PointwiseStatement() =>
        PrefixFormula(
            Seq(Call("h", F.Id("m")), Sp, Eq, Sp, F.Id("m")), true);
}
