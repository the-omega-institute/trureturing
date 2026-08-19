using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisot;

internal sealed class Beta13InfiniteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var q = Id("Q");
        var word = Id("w");
        var naturals = Id("N");
        var words = Call("List", Id("Z"));
        var beta = Id("beta13");
        Formula Remainder(Formula index) => Call("beta13RemainderValue", index);
        Formula Digit(Formula index) => Call("beta13GreedyDigit", index);
        Formula Prefix(Formula length) => Call("beta13GreedyPrefix", length);
        Formula ForAllNat(Formula body) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            naturals,
            body);

        var recurrence = ForAllNat(Equal(
            Remainder(Add(n, Num(1))),
            Subtract(Multiply(beta, Remainder(n)), Digit(n))));
        var interval = ForAllNat(new Formula.Logic(
            new Formula.Relation(Num(0), FormulaRelationOperator.LessThanOrEqual, Remainder(n)),
            FormulaLogicOperator.And,
            new Formula.Relation(Remainder(n), FormulaRelationOperator.LessThanOrEqual, Num(1))));
        var floorDigit = ForAllNat(Equal(
            Digit(n),
            new Formula.Floor(Multiply(beta, Remainder(n)))));
        var floorRecurrence = ForAllNat(Equal(
            Remainder(Add(n, Num(1))),
            Subtract(
                Multiply(beta, Remainder(n)),
                new Formula.Floor(Multiply(beta, Remainder(n))))));
        var prefixFromStream = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("Q"),
            naturals,
            Equal(Prefix(q), Call("ofFn", q, Id("beta13GreedyDigit"))));
        var allLengthCriterion = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("w"),
            words,
            new Formula.Logic(
                Equal(Call("beta13BelowGreedyPrefix", word), Id("true")),
                FormulaLogicOperator.Iff,
                NotEqual(
                    Call("compare", word,
                        Call("ofFn", Call("length", word), Id("beta13GreedyDigit"))),
                    Id("greater"))));
        var generatorCriterion = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("Q"),
            naturals,
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("w"),
                words,
                new Formula.Logic(
                    new Formula.Relation(
                        word,
                        FormulaRelationOperator.MemberOf,
                        Call("beta13Names", q)),
                    FormulaLogicOperator.Iff,
                    new Formula.Logic(
                        Equal(Call("length", word), q),
                        FormulaLogicOperator.And,
                        Call("Beta13Admissible", word)))));
        var countSix = Equal(
            Call("card", Call("beta13NormalizedGapSpectrum", Num(6))),
            Num(6));

        return DocumentDefinition.Create(ScribeNode.Create(
            "An exact quadratic-state recurrence defines the infinite greedy beta13 stream, "
                + "its all-length suffix criterion, and an independent level-six gap count.",
            H("Infinite Greedy Stream for Beta13"),
            Blocks(
                Paragraph(Text(
                    "Integer pairs encode every remainder exactly because beta13 squared is "
                        + "beta13 plus three. An executable integer comparison selects each floor "
                        + "digit without floating-point approximation.")),
                Describe.Lean(
                    DescribeId.Create("exact-remainder-recurrence"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13Infinite.beta13_remainder_value_succ"),
                    H("Exact remainder recurrence"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(recurrence)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The real interpretation of the next exact pair is beta13 times the "
                            + "current remainder minus the selected integer digit."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("remainders-stay-in-unit-interval"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13Infinite."
                            + "beta13_remainder_value_in_unit_interval"),
                    H("Remainders stay in the unit interval"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(interval)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Induction identifies every successor with a fractional part, so all "
                            + "remainders lie between zero and one."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("digits-are-greedy-floors"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13Infinite.beta13_greedy_digit_eq_floor"),
                    H("Every digit is the greedy floor digit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(floorDigit)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact sign comparison and the invariant interval identify the chosen "
                            + "digit with the real floor at every index."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("greedy-floor-recurrence"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13Infinite."
                            + "beta13_remainder_floor_recurrence"),
                    H("The stream obeys the greedy floor recurrence"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(floorRecurrence)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Substitution of the floor identity gives the standard greedy beta "
                            + "transformation recurrence for every natural index."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("threaded-prefix-is-infinite-stream-prefix"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13Infinite.beta13_greedy_prefix_eq_ofFn"),
                    H("Threaded prefixes come from the infinite stream"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(prefixFromStream)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The efficient state-threading implementation agrees pointwise with the "
                            + "unbounded digit function at every finite length."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("all-length-prefix-test"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13Infinite."
                            + "beta13_below_greedy_prefix_iff_infinite_stream"),
                    H("The prefix test is valid at every length"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(allLengthCriterion)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Unlike the frozen ten-digit list, the Boolean test compares each word "
                            + "with the equally long prefix of the infinite digit function."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("generator-matches-all-suffix-criterion"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13Infinite."
                            + "mem_beta13_names_iff_admissible"),
                    H("The generator matches the all-suffix criterion"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(generatorCriterion)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At every level, recursive generator membership is equivalent to the "
                            + "declared length, alphabet membership, and the infinite-prefix test "
                            + "for every suffix."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("independent-level-six-gap-count"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13Infinite."
                            + "beta13_infinite_gap_type_count_six"),
                    H("The infinite-prefix model has six level-six gap types"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(countSix)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A default-depth, chunked exact certificate recomputes the level-six "
                            + "spectrum without using any frozen gap-count theorem."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/NonPisot/Beta13")),
            ]));
    }
}
