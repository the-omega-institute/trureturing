using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class ControlledFiniteStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite controlled observations stabilize at the maximal common invariant relation.",
        H("Controlled Finite Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("controlled-finite-stability"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/ControlledFiniteStability."
                        + "controlled_finite_stability"),
                H("Controlled refinement stabilizes at the maximal common congruence"),
                StatementSource.FromAuthor(StabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the state, input, and realized readout carriers be finite and "
                            + "nonempty. Construct every bounded relation from equality of "
                            + "readouts after all input words up to the stated length, and "
                            + "construct the complete relation from all finite input words. "
                            + "Surjectivity of the readout records that the output carrier is "
                            + "its realized image.")),
                    Paragraph(Text(
                        "If two consecutive bounded relations agree, the relation is a fixed "
                            + "point of the controlled refinement operator, so every later "
                            + "bounded relation agrees with it. The complete relation is the "
                            + "operator's greatest fixed point and the greatest equivalence "
                            + "contained in the current-readout kernel that is preserved by "
                            + "every input transition.")),
                    Paragraph(Text(
                        "The least stable depth is characterized publicly by stability and "
                            + "minimality. Before that depth every strict refinement increases "
                            + "the finite quotient class count. The count begins at the number "
                            + "of realized readouts, ends at the complete behavior quotient, "
                            + "and never exceeds the state count, giving both displayed bounds.")),
                    Paragraph(Text(
                        "Repository search found and directly reuses the controlled-word "
                            + "semantics, the bounded relation recursion, the recursive "
                            + "signature correctness theorem, and the complete behavior "
                            + "quotient. Pinned Mathlib supplied Fintype.card_le_of_surjective, "
                            + "Fintype.bijective_iff_surjective_and_card, and Nat.sInf_mem. No "
                            + "single packaged theorem containing the branching fixed-point "
                            + "and quotient-bound clauses was found."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula StabilityFormula()
    {
        Formula states = F.Id("Y");
        Formula inputs = F.Id("U");
        Formula outputs = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula depth = F.Id("m");
        Formula offset = F.Id("r");
        Formula stableDepth = Seq(F.Id("m"), Underscore, Grp(Star), Caret, Grp(inputs));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula relation = Call("R", update, readout, depth);
        Formula relationNext = Call("R", update, readout, Seq(depth, Plus, D(1)));
        Formula stableRelation = Call("R", update, readout, stableDepth);
        Formula stableRelationNext =
            Call("R", update, readout, Seq(stableDepth, Plus, D(1)));
        Formula laterRelation =
            Call("R", update, readout, Seq(depth, Plus, offset));
        Formula limitRelation = Call("RInfinity", update, readout);
        Formula refinement = Call("RefinementOperator", update, readout);
        Formula stableEquivalences = Call("CommonStableEquivalences", update, readout);
        Formula limitCount = Call("card", Call("quotient", states, limitRelation));
        Formula outputCount = Call("card", outputs);
        Formula stateCount = Call("card", states);

        Formula permanent = Seq(
            Forall, Sp, depth, InMacro, Sp, naturals, Comma, Sp,
            relation, Sp, Eq, Sp, relationNext, Sp, Rightarrow, Sp,
            Forall, Sp, offset, InMacro, Sp, naturals, Comma, Sp,
            laterRelation, Sp, Eq, Sp, relation);
        Formula greatestFixedPoint = Seq(
            limitRelation, Sp, Eq, Sp, Call("gfp", refinement));
        Formula greatestStable = Call("IsGreatest", stableEquivalences, limitRelation);
        Formula leastStable = Seq(
            Open, stableRelation, Sp, Eq, Sp, stableRelationNext, Close, Sp, Land, Sp,
            Open, Forall, Sp, depth, InMacro, Sp, naturals, Comma, Sp,
            relation, Sp, Eq, Sp, relationNext, Sp, Rightarrow, Sp,
            stableDepth, Sp, Leq, Sp, depth, Close);
        Formula firstBound = Seq(
            stableDepth, Sp, Leq, Sp, limitCount, Sp, Minus, Sp, outputCount);
        Formula secondBound = Seq(
            limitCount, Sp, Minus, Sp, outputCount, Sp, Leq, Sp,
            stateCount, Sp, Minus, Sp, outputCount);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, states, Comma, Sp, inputs, Comma, Sp, outputs, Comma,
            RowBreak, Grp(),
            Call("FiniteNonempty", states), Comma, Sp,
            Call("FiniteNonempty", inputs), Comma, Sp,
            Call("FiniteNonempty", outputs), Comma, RowBreak, Grp(),
            update, Colon, Sp, inputs, Sp, To, Sp, states, Sp, To, Sp, states,
            Comma, Sp, readout, Colon, Sp, states, Sp, To, Sp, outputs,
            Comma, Sp, Call("Surjective", readout), Comma, RowBreak, Grp(),
            Open, permanent, Close, Sp, Land, RowBreak, Grp(),
            Open, greatestFixedPoint, Close, Sp, Land, RowBreak, Grp(),
            Open, greatestStable, Close, Sp, Land, RowBreak, Grp(),
            Open, leastStable, Close, Sp, Land, RowBreak, Grp(),
            Open, firstBound, Close, Sp, Land, RowBreak, Grp(),
            Open, secondBound, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
