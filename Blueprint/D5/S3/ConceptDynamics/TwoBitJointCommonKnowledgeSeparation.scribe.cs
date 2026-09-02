using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class TwoBitJointCommonKnowledgeSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/TwoBitJointCommonKnowledgeSeparation."
            + "two_bit_joint_common_knowledge_separation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two coordinate observers have complete pooled knowledge but only constant "
            + "common knowledge.",
        H("Two-Bit Joint and Common Knowledge Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-bit-joint-common-knowledge-separation"),
            DeclarationHandle.Create(Declaration),
            H("Pooled knowledge is complete while common knowledge is trivial"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state space is the Boolean square. The first observer reads only "
                        + "the first coordinate and the second observer reads only the second.")),
                Paragraph(Text(
                    "The joint readout kernel is equality, so every Boolean-valued state "
                        + "function is pooled-observable.")),
                Paragraph(Text(
                    "Alternating the two individual kernel relations connects every pair "
                        + "of states. The common coarsening is therefore universal, and its "
                        + "Boolean-valued observable functions are exactly the constants."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula first = new Formula.Subscript(F.Id("q"), D(1));
        Formula second = new Formula.Subscript(F.Id("q"), D(2));
        Formula pooled = new Formula.Subscript(F.Id("K"), F.Id("pool"));
        Formula common = new Formula.Subscript(F.Id("K"), F.Id("common"));
        Formula firstProjection = new Formula.Subscript(F.Id("pi"), D(1));
        Formula secondProjection = new Formula.Subscript(F.Id("pi"), D(2));
        Formula diagonal = new Formula.Subscript(F.Id("Delta"), state);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            state, Sp, Colon, Eq, Sp, F.Id("Bool"), Sp, Times, Sp, F.Id("Bool"), Comma,
            RowBreak, Grp(),
            first, Sp, Eq, Sp, firstProjection, Comma, Sp,
            second, Sp, Eq, Sp, secondProjection, Comma,
            RowBreak, Grp(),
            pooled, Sp, Eq, Sp, Call("ker", Call("conceptJoin", first, second)),
            Sp, Eq, Sp, diagonal, Comma,
            RowBreak, Grp(),
            Call("Obs", pooled), Sp, Eq, Sp, Call("Fun", state, F.Id("Bool")), Comma,
            RowBreak, Grp(),
            common, Sp, Eq, Sp, Call("ker", Call("commonCoarsening", first, second)),
            Sp, Eq, Sp, state, Sp, Times, Sp, state, Comma,
            RowBreak, Grp(),
            Call("Obs", common), Sp, Eq, Sp, Call("Const", state, F.Id("Bool")), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
