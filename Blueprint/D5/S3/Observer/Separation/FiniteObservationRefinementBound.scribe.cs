using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class FiniteObservationRefinementBoundDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite observation relations refine monotonically and reach their first stable depth "
            + "within the available quotient-class budget.",
        H("Finite Observation Refinement Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-observation-refinement-and-stability-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/FiniteObservationRefinementBound."
                        + "finite_observation_refinement_and_stability_bound"),
                H("Finite observation refinement and stability bound"),
                StatementSource.FromAuthor(RefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y and O be finite types, let Y be nonempty, let tau update the "
                            + "state, and let q map Y surjectively onto the actual readout image. "
                            + "Write E_m for equality of readout words through depth m, c_m for "
                            + "the number of E_m classes, and m_star for the least depth where "
                            + "E_m and E_(m+1) agree.")),
                    Paragraph(Text(
                        "Forgetting the latest readout gives a surjection from the depth-(m+1) "
                            + "quotient to the depth-m quotient, proving that the relations "
                            + "decrease and their class counts increase. Equality of consecutive "
                            + "class counts makes this forgetting map bijective and therefore "
                            + "forces equality of the two relations.")),
                    Paragraph(Text(
                        "The repository theorem infinite_relation_stabilizes supplies an "
                            + "inhabited set of stable depths. Pinned Mathlib then supplies "
                            + "Nat.sInf_mem for attainment of the least one, together with "
                            + "Fintype.bijective_iff_surjective_and_card and "
                            + "Fintype.card_le_of_surjective for the strict-growth count.")),
                    Paragraph(Text(
                        "Every depth before m_star consumes at least one new quotient class. "
                            + "Surjectivity identifies c_0 with the size of O, while every "
                            + "observation quotient has at most the size of Y. These facts yield "
                            + "both displayed inequalities without assuming a bound beyond the "
                            + "finite, nonempty state carrier and surjective readout fixed by the "
                            + "source section."))),
                DescribeRole.Theorem))));

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

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

    private static Formula RelationAt(Formula index) =>
        new Formula.Subscript(F.Id("E"), index);

    private static Formula CountAt(Formula index) =>
        new Formula.Subscript(F.Id("c"), index);

    private static Formula Cardinality(Formula type) =>
        Seq(Lvert, Sp, type, Sp, Rvert);

    private static Formula RefinementFormula()
    {
        Formula state = F.Id("Y");
        Formula output = F.Id("O");
        Formula index = F.Id("m");
        Formula otherIndex = F.Id("n");
        Formula update = Tau;
        Formula readout = F.Id("q");
        Formula stableIndex = new Formula.Subscript(F.Id("m"), Star);
        Formula relation = RelationAt(index);
        Formula successorRelation = RelationAt(Seq(index, Plus, D(1)));
        Formula stableRelation = RelationAt(stableIndex);
        Formula stableSuccessor = RelationAt(Seq(stableIndex, Plus, D(1)));
        Formula otherRelation = RelationAt(otherIndex);
        Formula otherSuccessor = RelationAt(Seq(otherIndex, Plus, D(1)));
        Formula stableCount = CountAt(stableIndex);
        Formula initialCount = CountAt(D(0));
        Formula classDifference = Seq(stableCount, Sp, Minus, Sp, initialCount);
        Formula carrierDifference = Seq(
            Cardinality(state), Sp, Minus, Sp, Cardinality(output));
        Formula stableDepthDefinition = Seq(
            stableIndex, Sp, Eq, Sp,
            Operatorname, Grp(F.Id("sInf")), Sp,
            OpenBrace, index, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Sp,
            Mid, Sp, relation, Sp, Eq, Sp, successorRelation, CloseBrace);
        Formula classCountDefinition = Seq(
            CountAt(index), Sp, Eq, Sp,
            Cardinality(Seq(state, Sp, Slash, Sp, relation)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Comma, Sp,
            Typeclass("Fintype", state), Sp,
            Typeclass("Fintype", output), Sp,
            Typeclass("Nonempty", state), Comma, RowBreak,
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            readout, Colon, Sp, state, Sp, To, Sp, output, Comma, Sp,
            Call("Surjective", readout), Comma, RowBreak,
            classCountDefinition, Comma, Sp,
            stableDepthDefinition, Comma, RowBreak,
            Open, Forall, Sp, index, Comma, Sp,
            successorRelation, Sp, Subseteq, Sp, relation, Close, Sp,
            Land, RowBreak,
            Open, Forall, Sp, index, Comma, Sp,
            CountAt(index), Sp, Leq, Sp, CountAt(Seq(index, Plus, D(1))), Close,
            Sp, Land, RowBreak,
            stableRelation, Sp, Eq, Sp, stableSuccessor, Sp, Land, RowBreak,
            Open, Forall, Sp, otherIndex, Comma, Sp,
            otherRelation, Sp, Eq, Sp, otherSuccessor, Sp, Rightarrow, Sp,
            stableIndex, Sp, Leq, Sp, otherIndex, Close, Sp, Land, RowBreak,
            stableIndex, Sp, Leq, Sp, classDifference, Sp, Land, RowBreak,
            classDifference, Sp, Leq, Sp, carrierDifference, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
