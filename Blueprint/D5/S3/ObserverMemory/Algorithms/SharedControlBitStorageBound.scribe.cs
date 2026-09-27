using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms;

internal sealed class SharedControlBitStorageBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/Algorithms/SharedControlBitStorageBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared control rewrites force a sharp product bound for two jointly faithful finite codes.",
        H("Shared Control-Bit Storage Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("control-rewrite"),
                Handle("controlRewrite"),
                H("A control bit is written into one data coordinate"),
                StatementSource.FromAuthor(ControlRewriteFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The rewrite indexed by i clears every data coordinate except i, copies "
                        + "the control bit into coordinate i, and then clears the control bit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shared-control-actions"),
                Handle("sharedControlActions"),
                H("The allowed translations and rewrites"),
                StatementSource.FromAuthor(ActionsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The action set contains translation by each data basis vector, translation "
                        + "by the control basis vector, and every indexed control rewrite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dynamically-closed"),
                Handle("DynamicallyClosed"),
                H("Every state action descends to the code"),
                StatementSource.FromAuthor(DynamicallyClosedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A code is dynamically closed when each allowed action has an induced update "
                        + "on code values, with the two routes from a state to a new code value equal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prefix-code"),
                Handle("prefixCode"),
                H("The prefix code"),
                StatementSource.FromAuthor(PrefixFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For h at most d, the prefix code retains the first h data coordinates and "
                        + "the shared control bit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("suffix-code"),
                Handle("suffixCode"),
                H("The suffix code"),
                StatementSource.FromAuthor(SuffixFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For h at most d, the suffix code retains data coordinates h through d minus "
                        + "one and the shared control bit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("shared-control-bit-storage-bound"),
                Handle("shared_control_bit_storage_bound"),
                H("Classification, storage lower bound, and attainment"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Translation closure makes each fiber relation a coset relation of a "
                            + "ZMod 2 subspace. Stability under the control rewrites then forces "
                            + "that subspace either into the data hyperplane or to be the whole state space.")),
                    Paragraph(Text(
                        "Conversely, every subspace of the data hyperplane, together with the whole "
                            + "state space, is realized by its finite quotient code. Translations descend "
                            + "by quotient addition, while each linear control rewrite vanishes on the data "
                            + "hyperplane and therefore descends as well. Equality of quotient values is "
                            + "exactly membership of the state difference in the chosen subspace.")),
                    Paragraph(Text(
                        "For two jointly faithful noninjective codes, their kernel subspaces meet "
                            + "only at zero. The dimension formula for a sum and intersection, "
                            + "together with quotient cardinality, gives the displayed storage product bound.")),
                    Paragraph(Text(
                        "Complementary prefix and suffix codes are dynamically closed and jointly "
                            + "injective. Each keeps the control bit, and their finite range sizes "
                            + "multiply to the lower bound."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(Declaration + name);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula Arrow(Formula source, Formula target) => Seq(Parenthesized(source), Sp, To, Sp, target);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula At(Formula function, params Formula[] args)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(args[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Subscripted(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula LambdaOf(Formula variable, Formula domain, Formula body) =>
        Parenthesized(Seq(Typed(variable, domain), Sp, Mapsto, Sp, body));

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Bit() => Call("ZMod", D(2));
    private static Formula Data(Formula dimension) => Arrow(Call("Fin", dimension), Bit());
    private static Formula State(Formula dimension) => Pair(Data(dimension), Bit());
    private static Formula Projection(Formula value, byte index) => Subscripted(value, D(index));
    private static Formula Code(Formula name, Formula proof, Formula state) =>
        At(Subscripted(name, proof), state);

    private static Formula ControlRewriteFormula()
    {
        Formula d = F.Id("d"), i = F.Id("i"), z = F.Id("z");
        return Disp(Seq(
            Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Typed(i, Call("Fin", d)), Comma, Sp,
            Typed(z, State(d)), Comma, RowBreak,
            At(Subscripted(F.Id("controlRewrite"), i), z), Sp, Eq, Sp,
            Pair(Call("single", i, Projection(z, 2)), D(0)), Dot));
    }

    private static Formula ActionsFormula()
    {
        Formula d = F.Id("d"), f = F.Id("f"), i = F.Id("i"), z = F.Id("z");
        Formula dataTranslation = Seq(
            Exists, Sp, Typed(i, Call("Fin", d)), Comma, Sp,
            f, Sp, Eq, Sp,
            LambdaOf(z, State(d), Seq(z, Sp, Plus, Sp, Pair(Call("single", i, D(1)), D(0)))));
        Formula controlTranslation = Seq(
            f, Sp, Eq, Sp,
            LambdaOf(z, State(d), Seq(z, Sp, Plus, Sp, Pair(D(0), D(1)))));
        Formula rewrite = Seq(
            Exists, Sp, Typed(i, Call("Fin", d)), Comma, Sp,
            f, Sp, Eq, Sp, Subscripted(F.Id("controlRewrite"), i));
        Formula actionSet = Seq(
            OpenBrace, Typed(f, Arrow(State(d), State(d))), Sp, Mid, Sp,
            Parenthesized(dataTranslation), Sp, Lor, Sp,
            Parenthesized(controlTranslation), Sp, Lor, Sp,
            Parenthesized(rewrite), CloseBrace);

        return Disp(Seq(
            Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Subscripted(F.Id("sharedControlActions"), d), Sp, Eq, Sp,
            actionSet, Dot));
    }

    private static Formula DynamicallyClosedFormula()
    {
        Formula d = F.Id("d"), u = F.Id("u"), f = F.Id("f"), update = F.Id("F");
        Formula closure = Seq(
            Forall, Sp, f, Sp, InMacro, Sp, Subscripted(F.Id("sharedControlActions"), d), Comma, Sp,
            Exists, Sp, Typed(update, Arrow(Alpha, Alpha)), Comma, Sp,
            u, Sp, Circ, Sp, f, Sp, Eq, Sp, update, Sp, Circ, Sp, u);

        return Disp(Seq(
            Forall, Sp, Typed(d, Nat()), Comma, Sp,
            Typed(Alpha, F.Id("Type")), Comma, Sp,
            Typed(u, Arrow(State(d), Alpha)), Comma, RowBreak,
            Call("DynamicallyClosed", u), Sp, Iff, Sp, closure, Dot));
    }

    private static Formula PrefixFormula()
    {
        Formula d = F.Id("d"), h = F.Id("h"), bound = F.Id("p");
        Formula z = F.Id("z"), i = F.Id("i");
        Formula retained = LambdaOf(
            i, Call("Fin", h), At(Projection(z, 1), Call("castLE", bound, i)));

        return Disp(Seq(
            Forall, Sp, Typed(d, Nat()), Comma, Sp, Typed(h, Nat()), Comma, Sp,
            Typed(bound, Seq(h, Sp, Leq, Sp, d)), Comma, Sp,
            Typed(z, State(d)), Comma, RowBreak,
            Code(F.Id("prefixCode"), bound, z), Sp, Eq, Sp,
            Pair(retained, Projection(z, 2)), Dot));
    }

    private static Formula SuffixFormula()
    {
        Formula d = F.Id("d"), h = F.Id("h"), bound = F.Id("p");
        Formula z = F.Id("z"), i = F.Id("i");
        Formula retained = LambdaOf(
            i, Call("Fin", Seq(d, Sp, Minus, Sp, h)), At(Projection(z, 1), Seq(h, Sp, Plus, Sp, i)));

        return Disp(Seq(
            Forall, Sp, Typed(d, Nat()), Comma, Sp, Typed(h, Nat()), Comma, Sp,
            Typed(bound, Seq(h, Sp, Leq, Sp, d)), Comma, Sp,
            Typed(z, State(d)), Comma, RowBreak,
            Code(F.Id("suffixCode"), bound, z), Sp, Eq, Sp,
            Pair(retained, Projection(z, 2)), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), h = F.Id("h"), z = F.Id("z"), zp = F.Id("y");
        Formula u = F.Id("u"), v = F.Id("v"), subspace = F.Id("K");
        Formula bound = Seq(h, Sp, Leq, Sp, d);
        Formula suffix = Subscripted(F.Id("suffixCode"), bound);
        Formula prefix = Subscripted(F.Id("prefixCode"), bound);
        Formula dataHyperplane = Call("range", Call("inl", Bit(), Data(d), Bit()));
        Formula quotient = Call("mkQ", subspace);
        Formula subspaceAllowed = Parenthesized(Seq(
            Parenthesized(Seq(subspace, Sp, Subseteq, Sp, dataHyperplane)), Sp, Lor, Sp,
            Parenthesized(Seq(subspace, Sp, Eq, Sp, Call("top")))));
        Formula quotientEquality = Parenthesized(Seq(
            Forall, Sp, Typed(z, State(d)), Comma, Sp, Typed(zp, State(d)), Comma, Sp,
            Parenthesized(Seq(At(quotient, z), Sp, Eq, Sp, At(quotient, zp))), Sp, Iff, Sp,
            Parenthesized(Seq(
                Parenthesized(Seq(z, Sp, Minus, Sp, zp)), Sp, InMacro, Sp, subspace))));
        Formula kernel = Seq(
            Exists, Sp, Typed(subspace, Call("Submodule", Bit(), State(d))), Comma, RowBreak,
            Parenthesized(Seq(
                Forall, Sp, Typed(z, State(d)), Comma, Sp, Typed(zp, State(d)), Comma, Sp,
                Parenthesized(Seq(At(u, z), Sp, Eq, Sp, At(u, zp))), Sp, Iff, Sp,
                Parenthesized(Seq(
                    Parenthesized(Seq(z, Sp, Minus, Sp, zp)), Sp, InMacro, Sp, subspace)))),
            Sp, Land, RowBreak,
            subspaceAllowed);
        Formula realizability = Seq(
            Forall, Sp, Typed(subspace, Call("Submodule", Bit(), State(d))), Comma, RowBreak,
            subspaceAllowed, Sp, Rightarrow, RowBreak,
            Parenthesized(Seq(
                Parenthesized(Call("DynamicallyClosed", quotient)), Sp, Land, RowBreak,
                quotientEquality)));
        Formula noninjective = Seq(
            Parenthesized(Seq(Neg, Sp, Call("Injective", u))), Sp, Land, Sp,
            Parenthesized(Seq(Neg, Sp, Call("Injective", v))));
        Formula storage = Seq(
            Parenthesized(noninjective), Sp, Rightarrow, Sp,
            Parenthesized(Seq(
                Power(D(2), Parenthesized(Seq(d, Sp, Plus, Sp, D(2)))), Sp, Leq, Sp,
                Parenthesized(Seq(
                    Call("ncard", Call("range", u)), Sp, Cdot, Sp,
                    Call("ncard", Call("range", v)))))));
        Formula attainment = Seq(
            Forall, Sp, Typed(h, Nat()), Comma, Sp,
            Parenthesized(Seq(
                Parenthesized(Seq(D(1), Sp, Leq, Sp, h)), Sp, Land, Sp,
                Parenthesized(Seq(
                    h, Sp, Leq, Sp, Parenthesized(Seq(d, Sp, Minus, Sp, D(1))))))),
            Sp, Rightarrow, RowBreak,
            Parenthesized(Seq(
                Parenthesized(Call("DynamicallyClosed", suffix)), Sp, Land, Sp,
                Parenthesized(Call("DynamicallyClosed", prefix)), Sp, Land, RowBreak,
                Parenthesized(Call("Injective",
                    LambdaOf(z, State(d), Pair(At(suffix, z), At(prefix, z))))), Sp, Land, RowBreak,
                Parenthesized(Seq(
                    Parenthesized(Seq(
                        Call("ncard", Call("range", suffix)), Sp, Cdot, Sp,
                        Call("ncard", Call("range", prefix)))), Sp, Eq, Sp,
                    Power(D(2), Parenthesized(Seq(d, Sp, Plus, Sp, D(2)))))))));
        Formula assumptions = Parenthesized(Seq(
            Call("DynamicallyClosed", u), Sp, Land, Sp,
            Call("DynamicallyClosed", v), Sp, Land, Sp,
            Call("Injective", LambdaOf(z, State(d), Pair(At(u, z), At(v, z))))));

        return Disp(Seq(
            Forall, Sp, Typed(d, Nat()), Comma, Sp,
            D(2), Sp, Leq, Sp, d, Comma, Sp,
            Typed(Alpha, F.Id("Type")), Comma, Sp,
            Typed(Beta, F.Id("Type")), Comma, Sp,
            OpenBracket, Call("Finite", Alpha), CloseBracket, Comma, Sp,
            OpenBracket, Call("Finite", Beta), CloseBracket, Comma, RowBreak,
            Typed(u, Arrow(State(d), Alpha)), Comma, Sp,
            Typed(v, Arrow(State(d), Beta)), Comma, RowBreak,
            assumptions, Sp, Rightarrow, RowBreak,
            Parenthesized(kernel), Sp, Land, RowBreak,
            Parenthesized(realizability), Sp, Land, RowBreak,
            Parenthesized(storage), Sp, Land, RowBreak,
            Parenthesized(attainment), Dot));
    }
}
