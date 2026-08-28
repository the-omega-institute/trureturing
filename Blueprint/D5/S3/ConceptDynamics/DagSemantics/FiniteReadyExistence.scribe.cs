using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class FiniteReadyExistenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/FiniteReadyExistence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonempty finite pending set has a ready minimum under a topological linear order.",
        H("Finite Ready Existence"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-pending-set-has-nonempty-frontier"),
            DeclarationHandle.Create(Prefix + "complement_frontier_nonempty"),
            H("A nonempty finite pending set has an executable node"),
            StatementSource.FromAuthor(ExistenceFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "On a linearly ordered carrier, assume every dependency edge strictly "
                        + "increases the identity coordinate. A nonempty finite pending set then "
                        + "has a minimum with no pending prerequisite.")),
                Paragraph(Text(
                    "That minimum witnesses nonemptiness of the executable frontier over the "
                        + "pending complement. Finiteness is carried by the Finset binder and the "
                        + "linear order remains an instance binder."))),
            DescribeRole.Theorem))));

    private static Formula ExistenceFormula()
    {
        Formula edge = F.Id("edge");
        Formula pending = F.Id("pending");
        Formula hypotheses = Seq(
            Call("StrictDependencyCoordinate", edge, F.Id("id")), Sp, Land, Sp,
            Call("Nonempty", pending));

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("V"), Sp, To, Sp, F.Id("V"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
            pending, Colon, Sp, Call("Finset", F.Id("V")), Comma, RowBreak, Grp(),
            OpenBracket, Call("LinearOrder", F.Id("V")), CloseBracket,
            Comma, RowBreak, Grp(), Open, hypotheses, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Call("Nonempty", Call("executableFrontier", edge,
                Call("complement", Call("coeSet", pending)), Call("coeSet", pending))), Dot));
    }
}
