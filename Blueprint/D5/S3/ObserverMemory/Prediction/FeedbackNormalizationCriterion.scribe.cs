using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FeedbackNormalizationCriterionDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Prediction/FeedbackNormalizationCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite feedback normalization is equivalent to prefix causality and sequential kernel factorization.",
        H("Feedback Normalization Criterion"),
        Blocks(
            Entry("dependent-prefix", "Prefix", "Dependent output and action prefixes",
                PrefixFormula(),
                "A prefix of length n is a dependent word on precisely the rounds whose indices are below n.",
                DescribeRole.Definition),
            Entry("prefix-restriction", "restrictPrefix", "Restriction to an initial prefix",
                RestrictPrefixFormula(),
                "A complete dependent word restricts to a prefix by evaluation at the underlying round index.",
                DescribeRole.Definition),
            Entry("word-splicing", "spliceWords", "Splicing at a round cut",
                SpliceWordsFormula(),
                "A prefix and a suffix beginning at the cut determine a complete dependent word.",
                DescribeRole.Definition),
            Entry("feedback-actions", "feedbackActions", "Actions selected by causal feedback",
                FeedbackActionsFormula(),
                "At round t, the feedback action is the strategy value on the output prefix strictly before t.",
                DescribeRole.Definition),
            Entry("feedback-mass", "feedbackMass", "Fed-back total mass",
                FeedbackMassFormula(),
                "The fed-back mass sums the response table over output words after substituting the causal action word.",
                DescribeRole.Definition),
            Entry("prefix-marginal", "prefixMarginal", "Point prefix marginal",
                PrefixMarginalFormula(),
                "The point prefix marginal sums the response table over complete output words with the specified restriction.",
                DescribeRole.Definition),
            Entry("prefix-event-marginal", "prefixEventMarginal", "Event prefix marginal",
                PrefixEventMarginalFormula(),
                "The event prefix marginal sums over complete output words whose restriction belongs to the event.",
                DescribeRole.Definition),
            Entry("single-cut-switch", "singleCutSwitch", "Single-cut feedback switch",
                SingleCutSwitchFormula(),
                "Before the cut the strategy follows u; from the cut onward it selects v or w according to the observed prefix event.",
                DescribeRole.Definition),
            Entry("feedback-normalization-criterion",
                "feedback_normalization_prefix_causality_sequential_kernels",
                "Feedback normalization, prefix causality, and sequential kernels",
                TheoremFormula(),
                "For finite nonempty dependent round alphabets and a nonnegative normalized response table, the four displayed conditions are equivalent.",
                DescribeRole.Theorem,
                "A single-cut switch has mass one plus the difference of its two prefix-event marginals. Singleton events therefore force future-action independence of every prefix marginal.",
                "Recursive marginalization yields normalized ratio kernels on positive parent prefixes and one fixed normalized extension on null parents. Conversely, backward summation of normalized kernels makes every causal feedback mass equal to one."))));

    private static DocumentBlock Entry(
        string id,
        string selector,
        string title,
        Formula formula,
        string first,
        DescribeRole role,
        params string[] rest)
    {
        var paragraphs = new List<DocumentBlock> { Paragraph(Text(first)) };
        paragraphs.AddRange(rest.Select(value => Paragraph(Text(value))));
        return Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Owner + selector),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(paragraphs.ToArray()),
            role);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Sp, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq(items.ToArray());
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);

    private static Formula Paren(Formula value) => Seq(Open, value, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(Paren(source), Sp, To, Sp, target);

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Sp, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula Nat => Seq(Mathbb, Sp, Grp(F.Id("N")));

    private static Formula Real => Seq(Mathbb, Sp, Grp(F.Id("R")));

    private static Formula Universe => OperatornameCall("Type");

    private static Formula OperatornameCall(string name) =>
        Seq(Operatorname, Sp, Grp(F.Id(name)));

    private static Formula Fin(Formula n) => Call("Fin", n);

    private static Formula Family(Formula family, Formula horizon) =>
        Arrow(Typed(F.Id("t"), Fin(horizon)), Sub(family, F.Id("t")));

    private static Formula FamilyType(Formula horizon) =>
        Arrow(Fin(horizon), Universe);

    private static Formula Prefix(Formula family, Formula n) =>
        Call("Prefix", family, n);

    private static Formula Restrict(Formula word, Formula n) =>
        Call("restrictPrefix", word, n);

    private static Formula Feedback(Formula table, Formula strategy) =>
        Call("feedbackMass", table, strategy);

    private static Formula PointMarginal(
        Formula table, Formula n, Formula prefix, Formula actions) =>
        Call("prefixMarginal", table, n, prefix, actions);

    private static Formula EventMarginal(
        Formula table, Formula n, Formula eventSet, Formula actions) =>
        Call("prefixEventMarginal", table, n, eventSet, actions);

    private static Formula SumOver(Formula variable, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(variable), Sp, body);

    private static Formula ProductOver(Formula variable, Formula body) =>
        Seq(Prod, Sp, Underscore, Grp(variable), Sp, body);

    private static Formula PrefixFormula()
    {
        Formula horizon = F.Id("T"), family = F.Id("X"), n = F.Id("n");
        Formula i = F.Id("i"), subtype = Call("Below", Fin(horizon), n);
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(family, FamilyType(horizon)), Comma, Sp,
            Typed(n, Nat), Comma, RowBreak, Grp(),
            Prefix(family, n), Sp, Eq, Sp,
            Arrow(Typed(i, subtype), Sub(family, i)), Dot));
    }

    private static Formula RestrictPrefixFormula()
    {
        Formula horizon = F.Id("T"), family = F.Id("X"), word = F.Id("x");
        Formula n = F.Id("n"), i = F.Id("i");
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(family, FamilyType(horizon)), Comma, Sp,
            Typed(word, Family(family, horizon)), Comma, Sp,
            Typed(n, Nat), Comma, Sp,
            Typed(i, Call("Below", Fin(horizon), n)), Comma, RowBreak, Grp(),
            At(Restrict(word, n), i), Sp, Eq, Sp, At(word, i), Dot));
    }

    private static Formula SpliceWordsFormula()
    {
        Formula horizon = F.Id("T"), family = F.Id("X"), n = F.Id("n");
        Formula prefix = F.Id("u"), suffix = F.Id("v"), i = F.Id("i");
        Formula condition = Seq(i, Lt, n);
        Formula branch = Seq(
            Operatorname, Sp, Grp(F.Id("if")), Sp, condition, Sp,
            Operatorname, Sp, Grp(F.Id("then")), Sp, Sub(prefix, i), Sp,
            Operatorname, Sp, Grp(F.Id("else")), Sp, Sub(suffix, i));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(family, FamilyType(horizon)), Comma, Sp,
            Typed(n, Nat), Comma, Sp,
            Typed(prefix, Prefix(family, n)), Comma, Sp,
            Typed(suffix, Arrow(Typed(i, Call("From", Fin(horizon), n)), Sub(family, i))),
            Comma, RowBreak, Grp(),
            Forall, Sp, Typed(i, Fin(horizon)), Comma, Sp,
            At(Call("spliceWords", n, prefix, suffix), i), Sp, Eq, Sp, branch, Dot));
    }

    private static Formula FeedbackActionsFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula strategy = F.Id("f"), word = F.Id("y"), t = F.Id("t");
        Formula strategyType = Arrow(Typed(t, Fin(horizon)),
            Arrow(Prefix(outputs, t), Sub(actions, t)));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, Sp,
            Typed(strategy, strategyType), Comma, Sp,
            Typed(word, Family(outputs, horizon)), Comma, RowBreak, Grp(),
            Forall, Sp, Typed(t, Fin(horizon)), Comma, Sp,
            At(Call("feedbackActions", strategy, word), t), Sp, Eq, Sp,
            At(At(strategy, t), Restrict(word, t)), Dot));
    }

    private static Formula FeedbackMassFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula table = F.Id("P"), strategy = F.Id("f"), word = F.Id("y");
        Formula tableType = Arrow(Family(outputs, horizon),
            Arrow(Family(actions, horizon), Real));
        Formula strategyType = Arrow(Typed(F.Id("t"), Fin(horizon)),
            Arrow(Prefix(outputs, F.Id("t")), Sub(actions, F.Id("t"))));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, Sp,
            Typeclass("FintypeFamily", outputs), Comma, Sp,
            Typed(table, tableType), Comma, Sp,
            Typed(strategy, strategyType), Comma, RowBreak, Grp(),
            Feedback(table, strategy), Sp, Eq, Sp,
            SumOver(word, At(At(table, word), Call("feedbackActions", strategy, word))), Dot));
    }

    private static Formula PrefixMarginalFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula table = F.Id("P"), n = F.Id("n"), prefix = F.Id("x");
        Formula actionWord = F.Id("a"), word = F.Id("y");
        Formula indicator = Sub(F.Id("mathbf"),
            Grp(Seq(Restrict(word, n), Eq, prefix)));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, Sp,
            Typeclass("FintypeFamily", outputs), Comma, Sp,
            Typeclass("DecidableEqFamily", outputs), Comma, Sp,
            Typed(table, Arrow(Family(outputs, horizon), Arrow(Family(actions, horizon), Real))),
            Comma, Sp, Typed(n, Nat), Comma, Sp,
            Typed(prefix, Prefix(outputs, n)), Comma, Sp,
            Typed(actionWord, Family(actions, horizon)), Comma, RowBreak, Grp(),
            PointMarginal(table, n, prefix, actionWord), Sp, Eq, Sp,
            SumOver(word, Seq(indicator, Sp, At(At(table, word), actionWord))), Dot));
    }

    private static Formula PrefixEventMarginalFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula table = F.Id("P"), n = F.Id("n"), eventSet = F.Id("E");
        Formula actionWord = F.Id("a"), word = F.Id("y");
        Formula indicator = Sub(F.Id("mathbf"),
            Grp(Seq(Restrict(word, n), Sp, InMacro, Sp, eventSet)));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, Sp,
            Typeclass("FintypeFamily", outputs), Comma, Sp,
            Typeclass("DecidableEqFamily", outputs), Comma, Sp,
            Typed(table, Arrow(Family(outputs, horizon), Arrow(Family(actions, horizon), Real))),
            Comma, Sp, Typed(n, Nat), Comma, Sp,
            Typed(eventSet, Call("Set", Prefix(outputs, n))), Comma, Sp,
            Typed(actionWord, Family(actions, horizon)), Comma, RowBreak, Grp(),
            EventMarginal(table, n, eventSet, actionWord), Sp, Eq, Sp,
            SumOver(word, Seq(indicator, Sp, At(At(table, word), actionWord))), Dot));
    }

    private static Formula SingleCutSwitchFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula n = F.Id("n"), prefix = F.Id("u"), left = F.Id("v");
        Formula right = F.Id("w"), eventSet = F.Id("E"), t = F.Id("t");
        Formula history = F.Id("x"), observed = Restrict(history, n);
        Formula value = Seq(
            Operatorname, Sp, Grp(F.Id("if")), Sp, t, Lt, n, Sp,
            Operatorname, Sp, Grp(F.Id("then")), Sp, Sub(prefix, t), Sp,
            Operatorname, Sp, Grp(F.Id("else")), Sp,
            Operatorname, Sp, Grp(F.Id("if")), Sp, observed, Sp, InMacro, Sp, eventSet, Sp,
            Operatorname, Sp, Grp(F.Id("then")), Sp, Sub(left, t), Sp,
            Operatorname, Sp, Grp(F.Id("else")), Sp, Sub(right, t));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, Sp,
            Typed(n, Nat), Comma, Sp,
            Typed(prefix, Prefix(actions, n)), Comma, Sp,
            Typed(left, Call("Suffix", actions, n)), Comma, Sp,
            Typed(right, Call("Suffix", actions, n)), Comma, Sp,
            Typed(eventSet, Call("Set", Prefix(outputs, n))), Comma, RowBreak, Grp(),
            Forall, Sp, Typed(t, Fin(horizon)), Comma, Sp,
            Typed(history, Prefix(outputs, t)), Comma, Sp,
            At(At(Call("singleCutSwitch", n, prefix, left, right, eventSet), t), history),
            Sp, Eq, Sp, value, Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula table = F.Id("P"), word = F.Id("y"), actionWord = F.Id("a");
        Formula t = F.Id("t"), n = F.Id("n"), prefix = F.Id("x");
        Formula strategy = F.Id("f"), leftWord = F.Id("b");
        Formula u = F.Id("u"), v = F.Id("v"), w = F.Id("w"), eventSet = F.Id("E");
        Formula kernel = F.Id("q"), history = F.Id("h"), output = F.Id("z");
        Formula finT = Fin(horizon);
        Formula actionFamily = Family(actions, horizon);
        Formula outputFamily = Family(outputs, horizon);
        Formula strategyType = Arrow(Typed(t, finT),
            Arrow(Prefix(outputs, t), Sub(actions, t)));
        Formula tableType = Arrow(outputFamily, Arrow(actionFamily, Real));

        Formula conditionOne = Seq(
            Forall, Sp, Typed(strategy, strategyType), Comma, Sp,
            Feedback(table, strategy), Sp, Eq, Sp, D(1));

        Formula conditionTwo = Seq(
            Forall, Sp, Typed(n, Nat), Comma, Sp,
            Paren(Seq(D(1), Sp, Leq, Sp, n, Sp, Land, Sp, n, Lt, horizon)), Sp,
            Rightarrow, Sp,
            Forall, Sp, Typed(u, Prefix(actions, n)), Comma, Sp,
            Typed(v, Call("Suffix", actions, n)), Comma, Sp,
            Typed(w, Call("Suffix", actions, n)), Comma, Sp,
            Typed(eventSet, Call("Set", Prefix(outputs, n))), Comma, Sp,
            Feedback(table, Call("singleCutSwitch", n, u, v, w, eventSet)),
            Sp, Eq, Sp, D(1));

        Formula agrees = Seq(
            Forall, Sp, Typed(t, finT), Comma, Sp,
            t, Lt, n, Sp, Rightarrow, Sp,
            At(actionWord, t), Sp, Eq, Sp, At(leftWord, t));
        Formula conditionThree = Seq(
            Forall, Sp, Typed(n, Nat), Comma, Sp,
            n, Sp, Leq, Sp, horizon, Sp, Rightarrow, Sp,
            Forall, Sp, Typed(prefix, Prefix(outputs, n)), Comma, Sp,
            Typed(actionWord, actionFamily), Comma, Sp,
            Typed(leftWord, actionFamily), Comma, Sp,
            Paren(agrees), Sp, Rightarrow, Sp,
            PointMarginal(table, n, prefix, actionWord), Sp, Eq, Sp,
            PointMarginal(table, n, prefix, leftWord));

        Formula kernelType = Arrow(Typed(t, finT),
            Arrow(Prefix(actions, Seq(t, Plus, D(1))),
                Arrow(Prefix(outputs, t), Arrow(Sub(outputs, t), Real))));
        Formula kernelAt = At(At(At(At(kernel, t), actionWord), history), output);
        Formula nonnegative = Seq(
            Forall, Sp, Typed(t, finT), Comma, Sp,
            Typed(actionWord, Prefix(actions, Seq(t, Plus, D(1)))), Comma, Sp,
            Typed(history, Prefix(outputs, t)), Comma, Sp,
            Typed(output, Sub(outputs, t)), Comma, Sp,
            D(0), Sp, Leq, Sp, kernelAt);
        Formula normalized = Seq(
            Forall, Sp, Typed(t, finT), Comma, Sp,
            Typed(actionWord, Prefix(actions, Seq(t, Plus, D(1)))), Comma, Sp,
            Typed(history, Prefix(outputs, t)), Comma, Sp,
            SumOver(Typed(output, Sub(outputs, t)), kernelAt), Sp, Eq, Sp, D(1));
        Formula factor = At(At(At(At(kernel, t),
            Restrict(actionWord, Seq(t, Plus, D(1)))), Restrict(word, t)), At(word, t));
        Formula factorization = Seq(
            Forall, Sp, Typed(word, outputFamily), Comma, Sp,
            Typed(actionWord, actionFamily), Comma, Sp,
            At(At(table, word), actionWord), Sp, Eq, Sp,
            ProductOver(Typed(t, finT), factor));
        Formula conditionFour = Seq(
            Exists, Sp, Typed(kernel, kernelType), Comma, Sp,
            Paren(nonnegative), Sp, Land, Sp,
            Paren(normalized), Sp, Land, Sp,
            Paren(factorization));

        Formula tfae = Call("TFAE",
            Seq(OpenBracket,
                Paren(conditionOne), Comma, RowBreak, Grp(),
                Paren(conditionTwo), Comma, RowBreak, Grp(),
                Paren(conditionThree), Comma, RowBreak, Grp(),
                Paren(conditionFour),
                CloseBracket));

        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            D(1), Sp, Leq, Sp, horizon, Comma, RowBreak, Grp(),
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, RowBreak, Grp(),
            Typeclass("FintypeFamily", actions), Comma, Sp,
            Typeclass("NonemptyFamily", actions), Comma, Sp,
            Typeclass("DecidableEqFamily", actions), Comma, RowBreak, Grp(),
            Typeclass("FintypeFamily", outputs), Comma, Sp,
            Typeclass("NonemptyFamily", outputs), Comma, Sp,
            Typeclass("DecidableEqFamily", outputs), Comma, RowBreak, Grp(),
            Typed(table, tableType), Comma, Sp,
            Paren(Seq(Forall, Sp, Typed(word, outputFamily), Comma, Sp,
                Typed(actionWord, actionFamily), Comma, Sp,
                D(0), Sp, Leq, Sp, At(At(table, word), actionWord))), Comma, RowBreak, Grp(),
            Paren(Seq(Forall, Sp, Typed(actionWord, actionFamily), Comma, Sp,
                SumOver(Typed(word, outputFamily), At(At(table, word), actionWord)),
                Sp, Eq, Sp, D(1))), Comma, RowBreak, Grp(),
            tfae, Dot));
    }
}
