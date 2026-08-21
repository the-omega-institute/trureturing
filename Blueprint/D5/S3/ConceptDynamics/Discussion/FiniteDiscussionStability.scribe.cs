using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Discussion;

internal sealed class FiniteDiscussionStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite discussion admits at most the initially unresolved number of strict refinements.",
        H("Finite Discussion Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-discussion-stability"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Discussion/FiniteDiscussionStability."
                        + "finite_discussion_stability"),
                H("Finite discussions have a sharp strict-refinement budget"),
                StatementSource.FromAuthor(StabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be a finite state space and let q_i : X -> C_i be the concept "
                            + "readout after i strict information-growth steps. Each readout is "
                            + "surjective, so its coordinate type records exactly its attained "
                            + "concept classes rather than unused labels.")),
                    Paragraph(Text(
                        "Every nonredundant message is represented by the repository's canonical "
                            + "StrictRefinement relation from q_i to q_(i+1). A refinement factor "
                            + "is surjective on effective coordinate types. If their finite "
                            + "cardinalities were equal, Mathlib's finite surjection criterion "
                            + "would make the factor bijective and its inverse would give the "
                            + "forbidden reverse refinement.")),
                    Paragraph(Text(
                        "Consequently every message increases the number of attained concept "
                            + "classes by at least one. The final class count is at most |X|, "
                            + "while surjectivity identifies the initial coordinate count with "
                            + "|Im(q_0)|. Therefore n <= |X| - |Im(q_0)|, exactly the finite "
                            + "discussion bound.")),
                    Paragraph(Text(
                        "Repository search supplied ConceptJoinUniversal.Refines and "
                            + "StrictRefinementCapability.StrictRefinement. Pinned Mathlib supplied "
                            + "Nat.bijective_iff_surjective_and_card, "
                            + "Nat.card_le_card_of_surjective, and Nat.card_congr; no existing "
                            + "declaration packages the arbitrary-discussion bound."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Cardinality(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula StabilityFormula()
    {
        Formula state = F.Id("X");
        Formula stepCount = F.Id("n");
        Formula index = F.Id("i");
        Formula coordinate = Sub(F.Id("C"), index);
        Formula readout = Sub(F.Id("q"), index);
        Formula nextReadout = Sub(F.Id("q"), Seq(index, Plus, D(1)));
        Formula initialReadout = Sub(F.Id("q"), D(0));
        Formula range = Call("Im", initialReadout);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, state, Close,
            CloseBracket, Comma, Sp,
            stepCount, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak,
            Open, Forall, Sp, index, Comma, Sp,
            D(0), Sp, Leq, Sp, index, Sp, Leq, Sp, stepCount, Comma, Sp,
            coordinate, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, coordinate, Comma, Sp,
            Call("Surjective", readout), Close, Sp, Land, RowBreak,
            Open, Forall, Sp, index, Comma, Sp,
            D(0), Sp, Leq, Sp, index, Sp, Lt, Sp, stepCount, Comma, Sp,
            Call("StrictRefinement", readout, nextReadout), Close, Sp,
            Rightarrow, RowBreak,
            stepCount, Sp, Leq, Sp, Cardinality(state), Sp, Minus, Sp,
            Cardinality(range), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
