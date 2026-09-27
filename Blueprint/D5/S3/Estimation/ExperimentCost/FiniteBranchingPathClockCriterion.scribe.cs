using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ExperimentCost;

internal sealed class FiniteBranchingPathClockCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/ExperimentCost/FiniteBranchingPathClockCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative clocks on finite words have equivalent path, depth, and sublevel criteria.",
        H("Finite-Branching Path Clock Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("path-clock"),
                Handle("pathClock"),
                H("Path clock"),
                StatementSource.FromAuthor(PathClockFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The clock of a finite word is the sum of the calibrated costs of its "
                        + "successive edges. The cost of a letter is evaluated on the complete "
                        + "prefix preceding that letter."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("minimum-path-clock"),
                Handle("minimumPathClock"),
                H("Minimum path clock at a depth"),
                StatementSource.FromAuthor(MinimumClockFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At each depth, the minimum is taken over every word on the finite "
                        + "nonempty alphabet. Thus the minimum is attained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-branching-path-clock-criterion"),
                Handle("finite_branching_path_clock_criterion"),
                H("Path divergence, depth control, and finite sublevels"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Nonnegative increments make clocks monotone under extension. Hence the "
                            + "minimum clock is monotone in depth, and divergence of these minima "
                            + "bounds every clock sublevel by a finite set of short words.")),
                    Paragraph(Text(
                        "A finite sublevel cannot contain all distinct prefixes of an infinite "
                            + "word. Conversely, bounded depth minima give nonempty finite level "
                            + "sets closed under restriction. Konig's infinity lemma selects a "
                            + "compatible sequence, producing an infinite word with bounded clock."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(Prefix + name);

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(Open, source, Close, Sp, To, Sp, target);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula ListOf(Formula type) => Call("List", type);

    private static Formula Clock(Formula calibration, Formula history) =>
        Seq(F.Id("T"), Underscore, Grp(calibration), Open, history, Close);

    private static Formula MinimumClock(Formula calibration, Formula depth) =>
        Seq(F.Id("g"), Underscore, Grp(calibration), Open, depth, Close);

    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Seq(Lambda, Sp, Typed(variable, type), Comma, Sp, body);

    private static Formula PathClockFormula()
    {
        Formula alphabet = F.Id("A"), calibration = F.Id("c"), history = F.Id("h");
        Formula index = F.Id("i");
        Formula list = ListOf(alphabet);
        Formula calibrationType = Arrow(list, Arrow(alphabet, Reals()));
        Formula indexType = Call("Fin", Call("length", history));
        Formula summand = Call("c", Call("take", history, index), Call("get", history, index));

        return Disp(Seq(
            Forall, Sp, Typed(alphabet, F.Id("Type")), Comma, Sp,
            Typed(calibration, calibrationType), Comma, Sp,
            Typed(history, list), Comma, RowBreak, Grp(),
            Clock(calibration, history), Sp, Eq, Sp,
            Sum, Sp, Underscore, Grp(Typed(index, indexType)), Sp, summand, Dot));
    }

    private static Formula MinimumClockFormula()
    {
        Formula alphabet = F.Id("A"), calibration = F.Id("c"), depth = F.Id("n");
        Formula word = F.Id("w");
        Formula wordType = Arrow(Call("Fin", depth), alphabet);

        return Disp(Seq(
            Forall, Sp, Typed(alphabet, F.Id("Type")), Comma, Sp,
            OpenBracket, Call("Fintype", alphabet), CloseBracket, Comma, Sp,
            OpenBracket, Call("Nonempty", alphabet), CloseBracket, Comma, RowBreak, Grp(),
            Typed(calibration, Arrow(ListOf(alphabet), Arrow(alphabet, Reals()))), Comma, Sp,
            Typed(depth, Naturals()), Comma, RowBreak, Grp(),
            MinimumClock(calibration, depth), Sp, Eq, Sp,
            Min, Sp, Underscore, Grp(Typed(word, wordType)), Sp,
            Clock(calibration, Call("ofFn", word)), Dot));
    }

    private static Formula CriterionFormula()
    {
        Formula alphabet = F.Id("A"), calibration = F.Id("c"), history = F.Id("h");
        Formula letter = F.Id("x"), depth = F.Id("n"), index = F.Id("i");
        Formula omega = F.Id("omega"), bound = F.Id("b");
        Formula list = ListOf(alphabet);
        Formula calibrationType = Arrow(list, Arrow(alphabet, Reals()));
        Formula omegaType = Arrow(Naturals(), alphabet);
        Formula nonnegative = Seq(
            Forall, Sp, Typed(history, list), Comma, Sp, Typed(letter, alphabet), Comma, Sp,
            D(0), Sp, Leq, Sp, Call("c", history, letter));
        Formula prefix = Call("ofFn", LambdaOf(index, Call("Fin", depth), Call("omega", index)));
        Formula pathDivergence = Seq(
            Forall, Sp, Typed(omega, omegaType), Comma, Sp,
            Call("Tendsto", LambdaOf(depth, Naturals(), Clock(calibration, prefix)),
                F.Id("atTop"), F.Id("atTop")));
        Formula minimumDivergence = Call(
            "Tendsto", LambdaOf(depth, Naturals(), MinimumClock(calibration, depth)),
            F.Id("atTop"), F.Id("atTop"));
        Formula sublevel = Seq(
            OpenBrace, Typed(history, list), Sp, Mid, Sp,
            Clock(calibration, history), Sp, Leq, Sp, bound, CloseBrace);
        Formula finiteSublevels = Seq(
            Forall, Sp, Typed(bound, Reals()), Comma, Sp, Call("Finite", sublevel));

        return Disp(Seq(
            Forall, Sp, Typed(alphabet, F.Id("Type")), Comma, Sp,
            OpenBracket, Call("Fintype", alphabet), CloseBracket, Comma, Sp,
            OpenBracket, Call("Nonempty", alphabet), CloseBracket, Comma, RowBreak, Grp(),
            Typed(calibration, calibrationType), Comma, Sp,
            Open, nonnegative, Close, Sp, Rightarrow, Sp, RowBreak, Grp(),
            Operatorname, Grp(F.Id("List"), Dot, F.Id("TFAE")), Open,
            pathDivergence, Comma, RowBreak, Grp(),
            minimumDivergence, Comma, RowBreak, Grp(),
            finiteSublevels, Close, Dot));
    }
}
