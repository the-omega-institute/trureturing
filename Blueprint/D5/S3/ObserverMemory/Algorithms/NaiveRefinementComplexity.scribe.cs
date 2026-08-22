using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class NaiveRefinementComplexityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signature refinement has linear rounds and the stated sorting and hashing costs.",
        H("Naive Refinement Complexity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("naive-refinement-complexity"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/NaiveRefinementComplexity."
                        + "naive_refinement_complexity"),
                H("Canonical refinement has the finite-system complexity bounds"),
                StatementSource.FromAuthor(ComplexityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Consider a filter-indexed family of finite nonempty deterministic "
                            + "state systems. Each readout is surjective onto its realized "
                            + "output carrier. The algorithm recursively labels a state by its "
                            + "current readout and the preceding label of its successor, and "
                            + "stops at the first unchanged partition.")),
                    Paragraph(Text(
                        "The sorting, hashing, and workspace assumptions concern independent "
                            + "one-round or one-state cost functions. Total sorting and expected "
                            + "hashing work are constructed by multiplying the corresponding "
                            + "round cost by the canonical number of rounds plus the initial "
                            + "labeling pass. Total workspace is constructed from one record per "
                            + "state.")),
                    Paragraph(Text(
                        "The imported finite-stability theorem bounds the first unchanged "
                            + "partition by the state count minus the realized-output count. "
                            + "Mathlib's IsBigO.mul then composes that pointwise round bound with "
                            + "the primitive cost assumptions, producing the three displayed "
                            + "resource bounds.")),
                    Paragraph(Text(
                        "Repository search directly found and applies controlled_finite_stability "
                            + "and its canonical stopping depth. Pinned Mathlib directly supplies "
                            + "IsBigO.mul, IsBigO.of_bound, and isBigO_refl. Loogle and LeanSearch "
                            + "executables were unavailable, and no single packaged theorem with "
                            + "all four clauses was found."))),
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

    private static Formula ComplexityFormula()
    {
        Formula index = F.Id("i");
        Formula states = new Formula.Subscript(F.Id("Y"), index);
        Formula outputs = new Formula.Subscript(F.Id("O"), index);
        Formula update = new Formula.Subscript(F.Id("tau"), index);
        Formula readout = new Formula.Subscript(F.Id("q"), index);
        Formula stateCount = new Formula.Subscript(F.Id("n"), index);
        Formula outputCount = Seq(Lvert, Sp, outputs, Sp, Rvert);
        Formula rounds = Call("refinementRounds", update, readout);
        Formula sortingRound = new Formula.Subscript(F.Id("s"), index);
        Formula hashingRound = new Formula.Subscript(F.Id("h"), index);
        Formula workspaceRecord = new Formula.Subscript(F.Id("w"), index);
        Formula roundFactor = Seq(
            Open, stateCount, Sp, Minus, Sp, outputCount, Sp, Plus, Sp, D(1), Close);
        Formula sortingTarget = Seq(
            stateCount, Sp, Times, Sp, roundFactor, Sp, Times, Sp,
            Log, Sp, stateCount);
        Formula hashingTarget = Seq(stateCount, Sp, Times, Sp, roundFactor);

        Formula primitiveBounds = Seq(
            sortingRound, Sp, InMacro, Sp,
            Call("BigO", Seq(stateCount, Log, Sp, stateCount)), Comma, Sp,
            hashingRound, Sp, InMacro, Sp, Call("BigO", stateCount), Comma, Sp,
            workspaceRecord, Sp, InMacro, Sp, Call("BigO", D(1)));
        Formula roundClause = Seq(
            rounds, Sp, Leq, Sp, stateCount, Minus, outputCount);
        Formula sortingClause = Seq(
            Call("sortingRefinementWork", rounds, sortingRound), Sp, InMacro, Sp,
            Call("BigO", sortingTarget));
        Formula workspaceClause = Seq(
            Call("refinementWorkspace", stateCount, workspaceRecord), Sp, InMacro, Sp,
            Call("BigO", stateCount));
        Formula hashingClause = Seq(
            Call("expectedHashRefinementWork", rounds, hashingRound), Sp, InMacro, Sp,
            Call("BigO", hashingTarget));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, index, Comma, Sp,
            Call("FiniteNonempty", states), Comma, Sp,
            Call("FiniteNonempty", outputs), Comma, RowBreak, Grp(),
            stateCount, Sp, Eq, Sp, Seq(Lvert, Sp, states, Sp, Rvert), Comma,
            RowBreak, Grp(),
            update, Colon, Sp, states, Sp, To, Sp, states, Comma, Sp,
            readout, Colon, Sp, states, Sp, To, Sp, outputs, Comma, Sp,
            Call("Surjective", readout), Comma, RowBreak, Grp(),
            primitiveBounds, Sp, Longrightarrow, RowBreak, Grp(),
            Open, roundClause, Close, Sp, Land, RowBreak, Grp(),
            Open, sortingClause, Close, Sp, Land, RowBreak, Grp(),
            Open, workspaceClause, Close, Sp, Land, RowBreak, Grp(),
            Open, hashingClause, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
