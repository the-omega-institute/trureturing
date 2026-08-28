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
        Formula stepCount = F.Id("steps");
        Formula index = F.Id("i");
        Formula coordinate = F.Id("Coordinate");
        Formula concept = F.Id("concept");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")), Caret, Grp(Star));
        Formula indexType = Call("Fin", Seq(stepCount, Plus, D(1)));
        Formula coordinateAtIndex = Call("Coordinate", index);
        Formula conceptAtIndex = Call("concept", index);
        Formula initialReadout = Call("concept", D(0));
        Formula range = Call("range", initialReadout);
        Formula castSucc = Seq(index, Dot, F.Id("castSucc"));
        Formula succ = Seq(index, Dot, F.Id("succ"));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Colon, Sp, type, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, state, Close,
            CloseBracket, Comma, Sp,
            stepCount, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, RowBreak, Grp(),
            coordinate, Colon, Sp, indexType, Sp, To, Sp, type, Comma, RowBreak, Grp(),
            concept, Colon, Sp,
            Open, index, Colon, Sp, indexType, Close, Sp, To, Sp,
            Call("Concept", state, coordinateAtIndex), Comma, RowBreak, Grp(),
            Open, Forall, Sp, index, Colon, Sp, indexType, Comma, Sp,
            Call("Surjective", conceptAtIndex), Close, Comma, RowBreak, Grp(),
            Open, Forall, Sp, index, Colon, Sp, Call("Fin", stepCount), Comma, Sp,
            Call("StrictRefinement", Call("concept", castSucc),
                Call("concept", succ)), Close, Comma, RowBreak, Grp(),
            stepCount, Sp, Leq, Sp, Cardinality(state), Sp, Minus, Sp,
            Cardinality(range), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
