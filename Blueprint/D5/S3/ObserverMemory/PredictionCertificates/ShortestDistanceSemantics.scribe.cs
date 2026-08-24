using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionCertificates;

internal sealed class ShortestDistanceSemanticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-mismatch distance exactly measures future separation and stable depth.",
        H("Shortest-Distance Semantics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("shortest-distance-exact-semantics"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionCertificates/"
                        + "ShortestDistanceSemantics.shortest_distance_exact_semantics"),
                H("First separation determines distance and stable depth"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite nonempty state carrier, tau its deterministic "
                            + "update, and q a readout. The imported canonical distance is "
                            + "the least future readout-mismatch time, with none representing "
                            + "infinity.")),
                    Paragraph(Text(
                        "The public statement gives both the existence criterion and the exact "
                            + "least-time characterization. Infinite distance is stated directly "
                            + "as equality at every future readout time.")),
                    Paragraph(Text(
                        "The canonical least observation-stability depth equals the largest "
                            + "finite pair distance. The finite supremum uses zero for infinite "
                            + "entries, so the separate no-distinguishable-pair clause yields the "
                            + "source convention that the depth is zero.")),
                    Paragraph(Text(
                        "The proof applies the existing infinity criterion and finite-history "
                            + "stability theorem. Pinned Mathlib's least-witness and finite-supremum "
                            + "lemmas bridge the two canonical depth objects; no distance, relation, "
                            + "or stability primitive is redeclared."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Applied(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula states = F.Id("Y");
        Formula outputs = F.Id("O");
        Formula update = Tau;
        Formula readout = F.Id("q");
        Formula first = F.Id("y");
        Formula second = Seq(F.Id("y"), Apos);
        Formula depth = F.Id("k");
        Formula earlier = F.Id("j");
        Formula pair = Seq(Open, first, Comma, Sp, second, Close);
        Formula distance = Seq(
            new Formula.Subscript(F.Id("d"), readout),
            Open, first, Comma, Sp, second, Close);
        Formula stableDepth = new Formula.Subscript(F.Id("m"), Star);
        Formula updateAtDepth = new Formula.Power(update, depth);
        Formula updateEarlier = new Formula.Power(update, earlier);
        Formula firstAtDepth = Applied(readout, Applied(updateAtDepth, first));
        Formula secondAtDepth = Applied(readout, Applied(updateAtDepth, second));
        Formula firstEarlier = Applied(readout, Applied(updateEarlier, first));
        Formula secondEarlier = Applied(readout, Applied(updateEarlier, second));
        Formula futureMismatch = Seq(
            Exists, Sp, depth, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            firstAtDepth, Sp, Neq, Sp, secondAtDepth);
        Formula leastMismatch = Seq(
            firstAtDepth, Sp, Neq, Sp, secondAtDepth, Sp, Land, Sp,
            Forall, Sp, earlier, Sp, Lt, Sp, depth, Comma, Sp,
            firstEarlier, Sp, Eq, Sp, secondEarlier);
        Formula allFutureEqual = Seq(
            Forall, Sp, depth, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            firstAtDepth, Sp, Eq, Sp, secondAtDepth);
        Formula finitePairExists = Seq(
            Exists, Sp, first, Comma, Sp, second, InMacro, Sp, states,
            Comma, Sp, distance, Sp, Lt, Sp, Infty);
        Formula finiteDistances = Seq(
            OpenBrace, distance, Sp, Mid, Sp,
            first, Comma, Sp, second, InMacro, Sp, states, Comma, Sp,
            distance, Sp, Lt, Sp, Infty, CloseBrace);
        Formula maximumClause = Seq(
            Open, finitePairExists, Close, Sp, Rightarrow, Sp,
            stableDepth, Sp, Eq, Sp, Max, finiteDistances);
        Formula noPairClause = Seq(
            Open, Forall, Sp, first, Comma, Sp, second, InMacro, Sp, states,
            Comma, Sp, distance, Sp, Eq, Sp, Infty, Close, Sp,
            Rightarrow, Sp, stableDepth, Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, states, Comma, Sp, outputs, Comma, RowBreak, Grp(),
            Call("FiniteNonempty", states), Comma, Sp,
            update, Colon, Sp, states, Sp, To, Sp, states, Comma, Sp,
            readout, Colon, Sp, states, Sp, To, Sp, outputs, Comma, RowBreak, Grp(),
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, states, Comma, Sp,
            Open, distance, Sp, Lt, Sp, Infty, Close, Sp, Leftrightarrow, Sp,
            Open, futureMismatch, Close, Comma, RowBreak, Grp(),
            Forall, Sp, depth, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Open, distance, Sp, Eq, Sp, depth, Close, Sp, Leftrightarrow, Sp,
            Open, leastMismatch, Close, Comma, RowBreak, Grp(),
            Open, distance, Sp, Eq, Sp, Infty, Close, Sp, Leftrightarrow, Sp,
            Open, allFutureEqual, Close, Comma, RowBreak, Grp(),
            Open, maximumClause, Close, Sp, Land, RowBreak, Grp(),
            Open, noPairClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
