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

    private static Formula Nat => Seq(Mathbb, Sp, Grp(F.Id("N")));

    private static Formula Real => Seq(Mathbb, Sp, Grp(F.Id("R")));

    private static Formula Universe => OperatornameCall("Type");

    private static Formula OperatornameCall(string name) =>
        Seq(Operatorname, Sp, Grp(F.Id(name)));

    private static Formula Fin(Formula n) => Call("Fin", n);

    private static Formula Family(Formula family, Formula horizon)
    {
        Formula t = F.Id("t");
        return Arrow(Typed(t, Fin(horizon)), At(family, t));
    }

    private static Formula FamilyType(Formula horizon) =>
        Arrow(Fin(horizon), Universe);

    private static Formula Val(Formula value) => Seq(value, Dot, F.Id("val"));

    private static Formula First(Formula value) => Seq(value, Dot, D(1));

    private static Formula Pair(Formula value, Formula certificate) =>
        Seq(Langle, Sp, value, Comma, Sp, certificate, Rangle);

    private static Formula BelowIndex(Formula index, Formula horizon, Formula n) =>
        Seq(OpenBrace, Typed(index, Fin(horizon)), Sp, Slash, Slash, Sp,
            Val(index), Sp, Lt, Sp, n, CloseBrace);

    private static Formula FromIndex(Formula index, Formula horizon, Formula n) =>
        Seq(OpenBrace, Typed(index, Fin(horizon)), Sp, Slash, Slash, Sp,
            n, Sp, Leq, Sp, Val(index), CloseBrace);

    private static Formula SuffixType(
        Formula family, Formula horizon, Formula n, Formula index) =>
        Arrow(Typed(index, FromIndex(index, horizon, n)), At(family, First(index)));

    private static Formula FamilyInstance(
        string className, Formula family, Formula horizon)
    {
        Formula t = F.Id("t");
        return Seq(OpenBracket, Forall, Sp, Typed(t, Fin(horizon)), Comma, Sp,
            Call(className, At(family, t)), CloseBracket);
    }

    private static Formula TextWord(string value) =>
        Seq(F.Text, Grp(F.Id(value)));

    private static Formula Conditional(
        Formula condition, Formula whenTrue, Formula whenFalse) =>
        Seq(TextWord("if"), Sp, condition, Sp,
            TextWord("then"), Sp, whenTrue, Sp,
            TextWord("else"), Sp, whenFalse);

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
        Formula i = F.Id("i"), subtype = BelowIndex(i, horizon, n);
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(family, FamilyType(horizon)), Comma, Sp,
            Typed(n, Nat), Comma, RowBreak, Grp(),
            Prefix(family, n), Sp, Eq, Sp,
            Arrow(Typed(i, subtype), At(family, First(i))), Dot));
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
            Typed(i, BelowIndex(i, horizon, n)), Comma, RowBreak, Grp(),
            At(Restrict(word, n), i), Sp, Eq, Sp, At(word, First(i)), Dot));
    }

    private static Formula SpliceWordsFormula()
    {
        Formula horizon = F.Id("T"), family = F.Id("X"), n = F.Id("n");
        Formula prefix = F.Id("u"), suffix = F.Id("v"), i = F.Id("i");
        Formula beforeCut = Seq(Val(i), Sp, Lt, Sp, n);
        Formula fromCut = Seq(n, Sp, Leq, Sp, Val(i));
        Formula branch = Conditional(
            beforeCut,
            At(prefix, Pair(i, beforeCut)),
            At(suffix, Pair(i, fromCut)));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(family, FamilyType(horizon)), Comma, Sp,
            Typed(n, Nat), Comma, Sp,
            Typed(prefix, Prefix(family, n)), Comma, Sp,
            Typed(suffix, SuffixType(family, horizon, n, i)),
            Comma, RowBreak, Grp(),
            Forall, Sp, Typed(i, Fin(horizon)), Comma, Sp,
            At(Call("spliceWords", n, prefix, suffix), i), Sp, Eq, Sp, branch, Dot));
    }

    private static Formula FeedbackActionsFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula strategy = F.Id("f"), word = F.Id("y"), t = F.Id("t");
        Formula strategyType = Arrow(Typed(t, Fin(horizon)),
            Arrow(Prefix(outputs, Val(t)), At(actions, t)));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, Sp,
            Typed(strategy, strategyType), Comma, Sp,
            Typed(word, Family(outputs, horizon)), Comma, RowBreak, Grp(),
            Forall, Sp, Typed(t, Fin(horizon)), Comma, Sp,
            At(Call("feedbackActions", strategy, word), t), Sp, Eq, Sp,
            At(At(strategy, t), Restrict(word, Val(t))), Dot));
    }

    private static Formula FeedbackMassFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula table = F.Id("P"), strategy = F.Id("f"), word = F.Id("y");
        Formula tableType = Arrow(Family(outputs, horizon),
            Arrow(Family(actions, horizon), Real));
        Formula t = F.Id("t");
        Formula strategyType = Arrow(Typed(t, Fin(horizon)),
            Arrow(Prefix(outputs, Val(t)), At(actions, t)));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, Sp,
            FamilyInstance("Fintype", outputs, horizon), Comma, Sp,
            Typed(table, tableType), Comma, Sp,
            Typed(strategy, strategyType), Comma, RowBreak, Grp(),
            Feedback(table, strategy), Sp, Eq, Sp,
            SumOver(Typed(word, Family(outputs, horizon)),
                At(At(table, word), Call("feedbackActions", strategy, word))), Dot));
    }

    private static Formula PrefixMarginalFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula table = F.Id("P"), n = F.Id("n"), prefix = F.Id("x");
        Formula actionWord = F.Id("a"), word = F.Id("y");
        Formula summand = Conditional(
            Seq(Restrict(word, n), Sp, Eq, Sp, prefix),
            At(At(table, word), actionWord),
            D(0));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, Sp,
            FamilyInstance("Fintype", outputs, horizon), Comma, Sp,
            FamilyInstance("DecidableEq", outputs, horizon), Comma, Sp,
            Typed(table, Arrow(Family(outputs, horizon), Arrow(Family(actions, horizon), Real))),
            Comma, Sp, Typed(n, Nat), Comma, Sp,
            Typed(prefix, Prefix(outputs, n)), Comma, Sp,
            Typed(actionWord, Family(actions, horizon)), Comma, RowBreak, Grp(),
            PointMarginal(table, n, prefix, actionWord), Sp, Eq, Sp,
            SumOver(Typed(word, Family(outputs, horizon)), summand), Dot));
    }

    private static Formula PrefixEventMarginalFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula table = F.Id("P"), n = F.Id("n"), eventSet = F.Id("E");
        Formula actionWord = F.Id("a"), word = F.Id("y");
        Formula summand = Conditional(
            Seq(Restrict(word, n), Sp, InMacro, Sp, eventSet),
            At(At(table, word), actionWord),
            D(0));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, Sp,
            FamilyInstance("Fintype", outputs, horizon), Comma, Sp,
            FamilyInstance("DecidableEq", outputs, horizon), Comma, Sp,
            Typed(table, Arrow(Family(outputs, horizon), Arrow(Family(actions, horizon), Real))),
            Comma, Sp, Typed(n, Nat), Comma, Sp,
            Typed(eventSet, Call("Set", Prefix(outputs, n))), Comma, Sp,
            Typed(actionWord, Family(actions, horizon)), Comma, RowBreak, Grp(),
            EventMarginal(table, n, eventSet, actionWord), Sp, Eq, Sp,
            SumOver(Typed(word, Family(outputs, horizon)), summand), Dot));
    }

    private static Formula SingleCutSwitchFormula()
    {
        Formula horizon = F.Id("T"), actions = F.Id("A"), outputs = F.Id("Y");
        Formula n = F.Id("n"), prefix = F.Id("u"), left = F.Id("v");
        Formula right = F.Id("w"), eventSet = F.Id("E"), t = F.Id("t");
        Formula i = F.Id("i"), history = F.Id("history"), observed = F.Id("x");
        Formula beforeCut = Seq(Val(t), Sp, Lt, Sp, n);
        Formula fromCut = Seq(n, Sp, Leq, Sp, Val(t));
        Formula historyIndex = Pair(
            First(i), Seq(Val(First(i)), Sp, Lt, Sp, Val(t)));
        Formula observedDefinition = Seq(
            LambdaLower, Sp, i, Sp, Mapsto, Sp, At(history, historyIndex));
        Formula suffixChoice = Conditional(
            Seq(observed, Sp, InMacro, Sp, eventSet),
            At(left, Pair(t, fromCut)),
            At(right, Pair(t, fromCut)));
        Formula value = Conditional(
            beforeCut,
            At(prefix, Pair(t, beforeCut)),
            Seq(TextWord("let"), Sp, Typed(observed, Prefix(outputs, n)), Sp,
                Colon, Eq, Sp, observedDefinition, Semi, Sp, suffixChoice));
        return Disp(Seq(
            Forall, Sp, Typed(horizon, Nat), Comma, Sp,
            Typed(actions, FamilyType(horizon)), Comma, Sp,
            Typed(outputs, FamilyType(horizon)), Comma, Sp,
            Typed(n, Nat), Comma, Sp,
            Typed(prefix, Prefix(actions, n)), Comma, Sp,
            Typed(left, SuffixType(actions, horizon, n, i)), Comma, Sp,
            Typed(right, SuffixType(actions, horizon, n, i)), Comma, Sp,
            Typed(eventSet, Call("Set", Prefix(outputs, n))), Comma, RowBreak, Grp(),
            Forall, Sp, Typed(t, Fin(horizon)), Comma, Sp,
            Typed(history, Prefix(outputs, Val(t))), Comma, Sp,
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
        Formula i = F.Id("i");
        Formula finT = Fin(horizon);
        Formula actionFamily = Family(actions, horizon);
        Formula outputFamily = Family(outputs, horizon);
        Formula strategyType = Arrow(Typed(t, finT),
            Arrow(Prefix(outputs, Val(t)), At(actions, t)));
        Formula tableType = Arrow(outputFamily, Arrow(actionFamily, Real));

        Formula conditionOne = Seq(
            Forall, Sp, Typed(strategy, strategyType), Comma, Sp,
            Feedback(table, strategy), Sp, Eq, Sp, D(1));

        Formula switchQuantifier = Seq(
            Forall, Sp, Typed(u, Prefix(actions, n)), Comma, Sp,
            Typed(v, SuffixType(actions, horizon, n, i)), Comma, Sp,
            Typed(w, SuffixType(actions, horizon, n, i)), Comma, Sp,
            Typed(eventSet, Call("Set", Prefix(outputs, n))), Comma, Sp,
            Feedback(table, Call("singleCutSwitch", n, u, v, w, eventSet)),
            Sp, Eq, Sp, D(1));
        Formula conditionTwo = Seq(
            Forall, Sp, Typed(n, Nat), Comma, Sp,
            Paren(Seq(D(1), Sp, Leq, Sp, n)), Sp, Rightarrow, Sp,
            Paren(Seq(
                Paren(Seq(n, Sp, Lt, Sp, horizon)), Sp, Rightarrow, Sp,
                Paren(switchQuantifier))));

        Formula agrees = Seq(
            Forall, Sp, Typed(i, finT), Comma, Sp,
            Paren(Seq(Val(i), Sp, Lt, Sp, n)), Sp, Rightarrow, Sp,
            Paren(Seq(At(actionWord, i), Sp, Eq, Sp, At(leftWord, i))));
        Formula causalQuantifier = Seq(
            Forall, Sp, Typed(prefix, Prefix(outputs, n)), Comma, Sp,
            Typed(actionWord, actionFamily), Comma, Sp,
            Typed(leftWord, actionFamily), Comma, Sp,
            Paren(agrees), Sp, Rightarrow, Sp,
            Paren(Seq(
                PointMarginal(table, n, prefix, actionWord), Sp, Eq, Sp,
                PointMarginal(table, n, prefix, leftWord))));
        Formula conditionThree = Seq(
            Forall, Sp, Typed(n, Nat), Comma, Sp,
            Paren(Seq(n, Sp, Leq, Sp, horizon)), Sp, Rightarrow, Sp,
            Paren(causalQuantifier));

        Formula kernelType = Arrow(Typed(t, finT),
            Arrow(Prefix(actions, Seq(Val(t), Sp, Plus, Sp, D(1))),
                Arrow(Prefix(outputs, Val(t)), Arrow(At(outputs, t), Real))));
        Formula kernelAt = At(At(At(At(kernel, t), actionWord), history), output);
        Formula nonnegative = Seq(
            Forall, Sp, Typed(t, finT), Comma, Sp,
            Typed(actionWord, Prefix(actions, Seq(Val(t), Sp, Plus, Sp, D(1)))), Comma, Sp,
            Typed(history, Prefix(outputs, Val(t))), Comma, Sp,
            Typed(output, At(outputs, t)), Comma, Sp,
            D(0), Sp, Leq, Sp, kernelAt);
        Formula normalized = Seq(
            Forall, Sp, Typed(t, finT), Comma, Sp,
            Typed(actionWord, Prefix(actions, Seq(Val(t), Sp, Plus, Sp, D(1)))), Comma, Sp,
            Typed(history, Prefix(outputs, Val(t))), Comma, Sp,
            SumOver(Typed(output, At(outputs, t)), kernelAt), Sp, Eq, Sp, D(1));
        Formula factor = At(At(At(At(kernel, t),
            Restrict(actionWord, Seq(Val(t), Sp, Plus, Sp, D(1)))),
            Restrict(word, Val(t))), At(word, t));
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

        Formula tfae = At(
            Seq(F.Id("List"), Dot, F.Id("TFAE")),
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
            FamilyInstance("Fintype", actions, horizon), Comma, Sp,
            FamilyInstance("Nonempty", actions, horizon), Comma, Sp,
            FamilyInstance("DecidableEq", actions, horizon), Comma, RowBreak, Grp(),
            FamilyInstance("Fintype", outputs, horizon), Comma, Sp,
            FamilyInstance("Nonempty", outputs, horizon), Comma, Sp,
            FamilyInstance("DecidableEq", outputs, horizon), Comma, RowBreak, Grp(),
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
