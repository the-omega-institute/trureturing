using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class ControlledDistinguishingDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shortest distinguishing input words characterize complete controlled behavior and its stabilization depth.",
        H("Controlled Distinguishing Depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shortest-input-words-characterize-controlled-stability"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/ControlledDistinguishingDepth."
                        + "controlled_shortest_intervention_witness"),
                H("Shortest distinguishing words determine controlled stability"),
                StatementSource.FromAuthor(DistinguishingDepthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the state, input, and realized readout carriers be finite and "
                            + "nonempty. An input word is applied from left to right through the "
                            + "canonical controlled transition semantics. The distance of a state "
                            + "pair is the least word length at which the two resulting readouts "
                            + "differ, and is infinite when no such word exists.")),
                    Paragraph(Text(
                        "A pair has infinite distance exactly when every finite input word gives "
                            + "equal readouts, which is membership in the canonical complete "
                            + "controlled relation. When at least one pair has finite distance, "
                            + "the source's least stable refinement depth is the maximum of those "
                            + "finite shortest-word distances.")),
                    Paragraph(Text(
                        "The proof directly applies the frozen controlled finite-stability theorem. "
                            + "Pinned Mathlib's Nat.find selects the least source-level separating "
                            + "word length, while the nonempty finite supremum supplies the latest "
                            + "such length. Repository and pinned-library searches found no theorem "
                            + "already packaging both branching-input clauses."))),
                DescribeRole.Theorem))));

    private static Formula Named(string name, params Formula[] arguments)
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

    private static Formula DistinguishingDepthFormula()
    {
        Formula states = F.Id("Y");
        Formula inputs = F.Id("U");
        Formula outputs = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula first = F.Id("y");
        Formula second = Seq(F.Id("y"), Apos);
        Formula pair = Seq(Open, first, Comma, Sp, second, Close);
        Formula finitePairs = Named("finitelyDistinguishablePairs", update, readout);
        Formula distance = Named("shortestDistinguishingDepth", update, readout, pair);
        Formula limitRelation = Named("controlledLimitRelation", update, readout);
        Formula stableDepth = Named("controlledStabilityDepth", update, readout);
        Formula maximumDistance = Seq(
            Max, Underscore, Grp(pair, Sp, InMacro, Sp, finitePairs), Sp, distance);

        Formula infiniteClause = Seq(
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, states, Comma, Sp,
            distance, Sp, Eq, Sp, Infty, Sp, Leftrightarrow, Sp,
            pair, Sp, InMacro, Sp, limitRelation);
        Formula maximumClause = Seq(
            finitePairs, Sp, Neq, Sp, Emptyset, Sp, Rightarrow, Sp,
            stableDepth, Sp, Eq, Sp, maximumDistance);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, states, Comma, Sp, inputs, Comma, Sp, outputs, Comma,
            RowBreak, Grp(),
            Named("FiniteNonempty", states), Comma, Sp,
            Named("FiniteNonempty", inputs), Comma, Sp,
            Named("FiniteNonempty", outputs), Comma, RowBreak, Grp(),
            update, Colon, Sp, inputs, Sp, To, Sp, states, Sp, To, Sp, states,
            Comma, Sp, readout, Colon, Sp, states, Sp, To, Sp, outputs,
            Comma, Sp, Named("Surjective", readout), Comma, RowBreak, Grp(),
            Open, infiniteClause, Close, Sp, Land, RowBreak, Grp(),
            Open, maximumClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
