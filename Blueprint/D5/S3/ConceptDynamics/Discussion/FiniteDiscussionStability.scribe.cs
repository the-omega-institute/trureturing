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

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var content = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) content.AddRange([Comma, Sp]);
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula StabilityFormula()
    {
        Formula state = F.Id("X");
        Formula stepCount = F.Id("steps");
        Formula index = F.Id("i");
        Formula coordinate = F.Id("Coordinate");
        Formula concept = F.Id("concept");
        Formula indexType = Call("Fin", Seq(stepCount, Sp, Plus, Sp, D(1)));
        Formula coordinateAtIndex = Apply(coordinate, index);
        Formula readout = Apply(concept, index);
        Formula nextReadout = Apply(concept, Call("succ", index));
        Formula initialReadout = Apply(concept, D(0));
        Formula range = Call("Im", initialReadout);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(state, type), Comma, Sp,
                OpenBracket, Call("Fintype", state), CloseBracket, Comma, Sp,
                Typed(stepCount, Seq(Mathbb, Grp(F.Id("N")))), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(coordinate, Arrow(indexType, type)), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(concept, Seq(Forall, Sp, Typed(index, indexType), Comma, Sp,
                    Call("Concept", state, coordinateAtIndex))), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(F.Id("effective"), Seq(Forall, Sp, Typed(index, indexType), Comma, Sp,
                    Call("Surjective", readout))), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(F.Id("strict"), Seq(
                    Forall, Sp, Typed(index, Call("Fin", stepCount)), Comma, Sp,
                    Call("StrictRefinement", Apply(concept, Call("castSucc", index)), nextReadout))),
                Comma),
            Seq(Grp(), stepCount, Sp, Leq, Sp, Cardinality(state), Sp, Minus, Sp,
                Cardinality(range), Dot),
        ]));
    }
}
