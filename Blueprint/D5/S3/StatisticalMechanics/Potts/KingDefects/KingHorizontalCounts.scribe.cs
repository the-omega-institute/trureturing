using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class KingHorizontalCountsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalCounts.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: KingHorizontalCounts"),
        Blocks(
            Node("interior_count_support", "interior count support", Formula0(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Sum the support counts over the two special ordered pairs."),
            Node("supports", "supports", Formula1(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The four supports in index order are empty, the singleton false, the singleton true, and the full Boolean set."),
            Node("lower_pair_values", "lower pair values", Formula2(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The six ordered pairs are obtained from the first colour, the second colour and their sum, in the displayed order."),
            Node("lower_pair_valid", "lower pair valid", Formula3(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Each of the six indexed pairs consists of distinct nonzero colours."),
            Node("lower_pair", "lower pair", Formula4(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Attach the nonzero and distinctness conditions to the indexed ordered pair."),
            Node("support_sizes", "support sizes", Formula5(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "This is a 6 by 4 by 4 table of pairs of natural numbers. The first index chooses the lower ordered pair and the next two choose Boolean supports; the two entries count the left and right shared horizontal alphabets."),
            Node("support_sizes_correct", "support sizes correct", Formula6(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Each table entry is exactly the pair of shared horizontal alphabet cardinalities for its ordered-pair case and two supports."),
            Node("support_case_count", "support case count", Formula7(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "For a fixed lower-pair case, sum the two support multiplicities times the two alphabet-size powers."),
            Node("pair_support_cases", "pair support cases", Formula8(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "For a fixed upper pair, the six lower-pair choices have the indicated support-table counts."),
            Node("P", "P", Formula9(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "If the final side is empty, the count is E with the indicated reordered lengths. Otherwise only empty ordinary vertical sides contribute choices."),
            Node("Q", "Q", Formula10(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Each factor records whether its opposite horizontal side is empty, with independent exponents a and b."),
            Node("six_case_value", "six case value", Formula11(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The six cases are E of a + b, the binary-word power, the two P terms and the two Q terms in the displayed order."),
            Node("support_case_eval", "support case eval", Formula12(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The finite support sum has six expressions, with empty sides included in E, P and Q."),
            Node("interior_count", "interior count", Formula13(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "There are six upper ordered-pair choices, and summing the six relative lower-pair cases gives the displayed expression."),
            Node("horizontal_two_rows", "horizontal two rows", Formula14(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "On two rows every horizontal defect is on a boundary; summing its position gives the binary-word factor."),
            Node("boundary_one_column", "boundary one column", Formula15(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "With one horizontal step, the boundary words disappear and the ordinary vertical word remains free."),
            Node("boundary_slots_one_column", "boundary slots one column", Formula16(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Valid boundary data with a single horizontal slot have six special-pair choices and a free binary vertical word."),
            Node("interior_one_column_count", "interior one column count", Formula17(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "With one horizontal step, the two boundary assignments have independent special pairs and vertical words."),
            Node("horizontal_two_columns", "horizontal two columns", Formula18(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Sum the two boundary rows and all interior rows for a rectangle with two columns."),
            Node("interior_three_rows_count", "interior three rows count", Formula19(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The unique interior row has no ordinary vertical words on either side of the defect."),
            Node("horizontal_three_rows", "horizontal three rows", Formula20(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Combine the two boundary-row counts with the unique interior-row count and sum all column positions."),
            Node("interior_endpoint_value", "interior endpoint value", Formula21(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "When a horizontal side is empty and both combined vertical and opposite horizontal lengths are positive, the six terms reduce to four powers of two."),
            Node("interior_middle_value", "interior middle value", Formula22(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "When both horizontal sides and the combined vertical length are positive, only the two empty-vertical-side indicators remain besides the powers of two."),
            Node("interior_row_sum", "interior row sum", Formula23(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Sum the endpoint and middle column counts along a fixed interior row."),
            Node("boundary_row_sum", "boundary row sum", Formula24(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The two boundary-side powers form geometric sums over all column positions."),
            Node("horizontal_sum", "horizontal sum", Formula25(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Add the boundary rows and all interior rows, including their endpoint corrections."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Formula0() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "c",
                    Q("Nat"),
                    All(
                        "d",
                        Q("Nat"),
                        Eq(
                            App(
                                Q("KingDifference.N_e"),
                                Typed(
                                    App(
                                        App(
                                            Q("KingGrid.Edge.H"),
                                            App(
                                                App(Q("KingHorizontal.cut_row"), Add(V("a"), Num("1"))),
                                                Add(V("b"), Num("1"))
                                            )
                                        ),
                                        App(App(Q("KingHorizontal.pivot"), V("c")), V("d"))
                                    ),
                                    App(
                                        App(
                                            Q("KingGrid.Edge"),
                                            Add(Add(Add(V("a"), Num("1")), Add(V("b"), Num("1"))), Num("1"))
                                        ),
                                        Add(Add(V("c"), Add(V("d"), Num("1"))), Num("1"))
                                    )
                                )
                            ),
                            SumOver(
                                "x",
                                Q("KingDifference.NZPair"),
                                SumOver(
                                    "y",
                                    Q("KingDifference.NZPair"),
                                    App(
                                        App(
                                            App(
                                                App(
                                                    App(
                                                        App(Q("KingHorizontal.pair_support_count"), V("a")),
                                                        V("b")
                                                    ),
                                                    V("c")
                                                ),
                                                V("d")
                                            ),
                                            V("x")
                                        ),
                                        V("y")
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula1() =>
        And(
            Typed(
                Call("KingHorizontal.supports"),
                Arrow(App(Q("Fin"), Num("4")), App(Q("Finset"), Q("Bool")))
            ),
            And(
                Eq(Call("KingHorizontal.supports", Typed(Num("0"), Call("Fin", Num("4")))), Q("Finset.empty")),
                And(
                    Eq(
                        Call("KingHorizontal.supports", Typed(Num("1"), Call("Fin", Num("4")))),
                        Set(Q("Bool.false"))
                    ),
                    And(
                        Eq(
                            Call("KingHorizontal.supports", Typed(Num("2"), Call("Fin", Num("4")))),
                            Set(Q("Bool.true"))
                        ),
                        Eq(
                            Call("KingHorizontal.supports", Typed(Num("3"), Call("Fin", Num("4")))),
                            Typed(Q("Finset.univ"), App(Q("Finset"), Q("Bool")))
                        )
                    )
                )
            )
        );

    private static Formula Formula2() =>
        All(
            "x",
            Q("KingDifference.NZPair"),
            And(
                Typed(
                    Call("KingHorizontal.lower_pair_values", V("x")),
                    Arrow(App(Q("Fin"), Num("6")), Product(Q("KingDifference.K"), Q("KingDifference.K")))
                ),
                And(
                    Eq(
                        Call(
                            "KingHorizontal.lower_pair_values",
                            V("x"),
                            Typed(Num("0"), Call("Fin", Num("6")))
                        ),
                        Pair(
                            Call("Prod.fst", Call("Subtype.val", V("x"))),
                            Call("Prod.snd", Call("Subtype.val", V("x")))
                        )
                    ),
                    And(
                        Eq(
                            Call(
                                "KingHorizontal.lower_pair_values",
                                V("x"),
                                Typed(Num("1"), Call("Fin", Num("6")))
                            ),
                            Pair(
                                Call("Prod.snd", Call("Subtype.val", V("x"))),
                                Call("Prod.fst", Call("Subtype.val", V("x")))
                            )
                        ),
                        And(
                            Eq(
                                Call(
                                    "KingHorizontal.lower_pair_values",
                                    V("x"),
                                    Typed(Num("2"), Call("Fin", Num("6")))
                                ),
                                Pair(
                                    Call("Prod.fst", Call("Subtype.val", V("x"))),
                                    Add(
                                        Call("Prod.fst", Call("Subtype.val", V("x"))),
                                        Call("Prod.snd", Call("Subtype.val", V("x")))
                                    )
                                )
                            ),
                            And(
                                Eq(
                                    Call(
                                        "KingHorizontal.lower_pair_values",
                                        V("x"),
                                        Typed(Num("3"), Call("Fin", Num("6")))
                                    ),
                                    Pair(
                                        Add(
                                            Call("Prod.fst", Call("Subtype.val", V("x"))),
                                            Call("Prod.snd", Call("Subtype.val", V("x")))
                                        ),
                                        Call("Prod.snd", Call("Subtype.val", V("x")))
                                    )
                                ),
                                And(
                                    Eq(
                                        Call(
                                            "KingHorizontal.lower_pair_values",
                                            V("x"),
                                            Typed(Num("4"), Call("Fin", Num("6")))
                                        ),
                                        Pair(
                                            Add(
                                                Call("Prod.fst", Call("Subtype.val", V("x"))),
                                                Call("Prod.snd", Call("Subtype.val", V("x")))
                                            ),
                                            Call("Prod.fst", Call("Subtype.val", V("x")))
                                        )
                                    ),
                                    Eq(
                                        Call(
                                            "KingHorizontal.lower_pair_values",
                                            V("x"),
                                            Typed(Num("5"), Call("Fin", Num("6")))
                                        ),
                                        Pair(
                                            Call("Prod.snd", Call("Subtype.val", V("x"))),
                                            Add(
                                                Call("Prod.fst", Call("Subtype.val", V("x"))),
                                                Call("Prod.snd", Call("Subtype.val", V("x")))
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula3() =>
        All(
            "x",
            Q("KingDifference.NZPair"),
            All(
                "i",
                App(Q("Fin"), Num("6")),
                And(
                    Ne(
                        Call("Prod.fst", App(App(Q("KingHorizontal.lower_pair_values"), V("x")), V("i"))),
                        Num("0")
                    ),
                    And(
                        Ne(
                            Call("Prod.snd", App(App(Q("KingHorizontal.lower_pair_values"), V("x")), V("i"))),
                            Num("0")
                        ),
                        Ne(
                            Call("Prod.fst", App(App(Q("KingHorizontal.lower_pair_values"), V("x")), V("i"))),
                            Call("Prod.snd", App(App(Q("KingHorizontal.lower_pair_values"), V("x")), V("i")))
                        )
                    )
                )
            )
        );

    private static Formula Formula4() =>
        All(
            "x",
            Q("KingDifference.NZPair"),
            All(
                "i",
                App(Q("Fin"), Num("6")),
                And(
                    Typed(Call("KingHorizontal.lower_pair", V("x"), V("i")), Q("KingDifference.NZPair")),
                    Eq(
                        Call("Subtype.val", Call("KingHorizontal.lower_pair", V("x"), V("i"))),
                        Call("KingHorizontal.lower_pair_values", V("x"), V("i"))
                    )
                )
            )
        );

    private static Formula Formula5() =>
        Typed(
            Q("KingHorizontal.support_sizes"),
            Arrow(
                App(Q("Fin"), Num("6")),
                Arrow(App(Q("Fin"), Num("4")), Arrow(App(Q("Fin"), Num("4")), Product(Q("Nat"), Q("Nat"))))
            )
        );

    private static Formula Formula6() =>
        All(
            "x",
            Q("KingDifference.NZPair"),
            All(
                "i",
                App(Q("Fin"), Num("6")),
                All(
                    "j",
                    App(Q("Fin"), Num("4")),
                    All(
                        "k",
                        App(Q("Fin"), Num("4")),
                        Eq(
                            Pair(
                                App(
                                    Q("Nat.card"),
                                    App(
                                        App(
                                            App(
                                                App(
                                                    App(
                                                        App(Q("KingHorizontal.SupportAlphabet"), V("x")),
                                                        App(
                                                            App(Q("KingHorizontal.lower_pair"), V("x")),
                                                            V("i")
                                                        )
                                                    ),
                                                    App(Q("KingHorizontal.supports"), V("j"))
                                                ),
                                                App(Q("KingHorizontal.supports"), V("k"))
                                            ),
                                            Call("Prod.fst", Call("Subtype.val", V("x")))
                                        ),
                                        Call(
                                            "Prod.fst",
                                            Call(
                                                "Subtype.val",
                                                App(App(Q("KingHorizontal.lower_pair"), V("x")), V("i"))
                                            )
                                        )
                                    )
                                ),
                                App(
                                    Q("Nat.card"),
                                    App(
                                        App(
                                            App(
                                                App(
                                                    App(
                                                        App(Q("KingHorizontal.SupportAlphabet"), V("x")),
                                                        App(
                                                            App(Q("KingHorizontal.lower_pair"), V("x")),
                                                            V("i")
                                                        )
                                                    ),
                                                    App(Q("KingHorizontal.supports"), V("j"))
                                                ),
                                                App(Q("KingHorizontal.supports"), V("k"))
                                            ),
                                            Call("Prod.snd", Call("Subtype.val", V("x")))
                                        ),
                                        Call(
                                            "Prod.snd",
                                            Call(
                                                "Subtype.val",
                                                App(App(Q("KingHorizontal.lower_pair"), V("x")), V("i"))
                                            )
                                        )
                                    )
                                )
                            ),
                            App(App(App(Q("KingHorizontal.support_sizes"), V("i")), V("j")), V("k"))
                        )
                    )
                )
            )
        );

    private static Formula Formula7() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "c",
                    Q("Nat"),
                    All(
                        "d",
                        Q("Nat"),
                        All(
                            "i",
                            App(Q("Fin"), Num("6")),
                            Eq(
                                Call(
                                    "KingHorizontal.support_case_count",
                                    V("a"),
                                    V("b"),
                                    V("c"),
                                    V("d"),
                                    V("i")
                                ),
                                SumOver(
                                    "j",
                                    App(Q("Fin"), Num("4")),
                                    SumOver(
                                        "k",
                                        App(Q("Fin"), Num("4")),
                                        Mul(
                                            Mul(
                                                Mul(
                                                    App(
                                                        App(Q("KingHorizontal.support_weight"), V("a")),
                                                        App(Q("KingHorizontal.supports"), V("j"))
                                                    ),
                                                    App(
                                                        App(Q("KingHorizontal.support_weight"), V("b")),
                                                        App(Q("KingHorizontal.supports"), V("k"))
                                                    )
                                                ),
                                                Power(
                                                    Call(
                                                        "Prod.fst",
                                                        App(
                                                            App(
                                                                App(Q("KingHorizontal.support_sizes"), V("i")),
                                                                V("j")
                                                            ),
                                                            V("k")
                                                        )
                                                    ),
                                                    V("c")
                                                )
                                            ),
                                            Power(
                                                Call(
                                                    "Prod.snd",
                                                    App(
                                                        App(
                                                            App(Q("KingHorizontal.support_sizes"), V("i")),
                                                            V("j")
                                                        ),
                                                        V("k")
                                                    )
                                                ),
                                                V("d")
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula8() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "c",
                    Q("Nat"),
                    All(
                        "d",
                        Q("Nat"),
                        All(
                            "x",
                            Q("KingDifference.NZPair"),
                            All(
                                "i",
                                App(Q("Fin"), Num("6")),
                                Eq(
                                    App(
                                        App(
                                            App(
                                                App(
                                                    App(
                                                        App(Q("KingHorizontal.pair_support_count"), V("a")),
                                                        V("b")
                                                    ),
                                                    V("c")
                                                ),
                                                V("d")
                                            ),
                                            V("x")
                                        ),
                                        App(App(Q("KingHorizontal.lower_pair"), V("x")), V("i"))
                                    ),
                                    App(
                                        App(
                                            App(
                                                App(
                                                    App(Q("KingHorizontal.support_case_count"), V("a")),
                                                    V("b")
                                                ),
                                                V("c")
                                            ),
                                            V("d")
                                        ),
                                        V("i")
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula9() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "c",
                    Q("Nat"),
                    All(
                        "d",
                        Q("Nat"),
                        Eq(
                            Call("KingHorizontal.P", V("a"), V("b"), V("c"), V("d")),
                            Call(
                                "ite",
                                Eq(V("d"), Num("0")),
                                App(App(App(Q("KingHorizontal.E"), V("c")), V("a")), V("b")),
                                Power(
                                    Add(
                                        Call("ite", Eq(V("a"), Num("0")), Num("1"), Num("0")),
                                        Call("ite", Eq(V("b"), Num("0")), Num("1"), Num("0"))
                                    ),
                                    V("c")
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula10() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "c",
                    Q("Nat"),
                    All(
                        "d",
                        Q("Nat"),
                        Eq(
                            Call("KingHorizontal.Q", V("a"), V("b"), V("c"), V("d")),
                            Mul(
                                Power(
                                    Add(Num("1"), Call("ite", Eq(V("c"), Num("0")), Num("1"), Num("0"))),
                                    V("a")
                                ),
                                Power(
                                    Add(Num("1"), Call("ite", Eq(V("d"), Num("0")), Num("1"), Num("0"))),
                                    V("b")
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula11() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "c",
                    Q("Nat"),
                    All(
                        "d",
                        Q("Nat"),
                        And(
                            Typed(
                                Call("KingHorizontal.six_case_value", V("a"), V("b"), V("c"), V("d")),
                                Arrow(App(Q("Fin"), Num("6")), Q("Nat"))
                            ),
                            And(
                                Eq(
                                    Call(
                                        "KingHorizontal.six_case_value",
                                        V("a"),
                                        V("b"),
                                        V("c"),
                                        V("d"),
                                        Typed(Num("0"), Call("Fin", Num("6")))
                                    ),
                                    App(App(App(Q("KingHorizontal.E"), Add(V("a"), V("b"))), V("c")), V("d"))
                                ),
                                And(
                                    Eq(
                                        Call(
                                            "KingHorizontal.six_case_value",
                                            V("a"),
                                            V("b"),
                                            V("c"),
                                            V("d"),
                                            Typed(Num("1"), Call("Fin", Num("6")))
                                        ),
                                        Power(Num("2"), Add(V("a"), V("b")))
                                    ),
                                    And(
                                        Eq(
                                            Call(
                                                "KingHorizontal.six_case_value",
                                                V("a"),
                                                V("b"),
                                                V("c"),
                                                V("d"),
                                                Typed(Num("2"), Call("Fin", Num("6")))
                                            ),
                                            App(
                                                App(App(App(Q("KingHorizontal.P"), V("a")), V("b")), V("c")),
                                                V("d")
                                            )
                                        ),
                                        And(
                                            Eq(
                                                Call(
                                                    "KingHorizontal.six_case_value",
                                                    V("a"),
                                                    V("b"),
                                                    V("c"),
                                                    V("d"),
                                                    Typed(Num("3"), Call("Fin", Num("6")))
                                                ),
                                                App(
                                                    App(
                                                        App(App(Q("KingHorizontal.P"), V("a")), V("b")),
                                                        V("d")
                                                    ),
                                                    V("c")
                                                )
                                            ),
                                            And(
                                                Eq(
                                                    Call(
                                                        "KingHorizontal.six_case_value",
                                                        V("a"),
                                                        V("b"),
                                                        V("c"),
                                                        V("d"),
                                                        Typed(Num("4"), Call("Fin", Num("6")))
                                                    ),
                                                    App(
                                                        App(
                                                            App(App(Q("KingHorizontal.Q"), V("a")), V("b")),
                                                            V("c")
                                                        ),
                                                        V("d")
                                                    )
                                                ),
                                                Eq(
                                                    Call(
                                                        "KingHorizontal.six_case_value",
                                                        V("a"),
                                                        V("b"),
                                                        V("c"),
                                                        V("d"),
                                                        Typed(Num("5"), Call("Fin", Num("6")))
                                                    ),
                                                    App(
                                                        App(
                                                            App(App(Q("KingHorizontal.Q"), V("a")), V("b")),
                                                            V("d")
                                                        ),
                                                        V("c")
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula12() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "c",
                    Q("Nat"),
                    All(
                        "d",
                        Q("Nat"),
                        All(
                            "i",
                            App(Q("Fin"), Num("6")),
                            Eq(
                                App(
                                    App(
                                        App(
                                            App(App(Q("KingHorizontal.support_case_count"), V("a")), V("b")),
                                            V("c")
                                        ),
                                        V("d")
                                    ),
                                    V("i")
                                ),
                                App(
                                    App(
                                        App(
                                            App(App(Q("KingHorizontal.six_case_value"), V("a")), V("b")),
                                            V("c")
                                        ),
                                        V("d")
                                    ),
                                    V("i")
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula13() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "c",
                    Q("Nat"),
                    All(
                        "d",
                        Q("Nat"),
                        Eq(
                            App(
                                Q("KingDifference.N_e"),
                                Typed(
                                    App(
                                        App(
                                            Q("KingGrid.Edge.H"),
                                            App(
                                                App(Q("KingHorizontal.cut_row"), Add(V("a"), Num("1"))),
                                                Add(V("b"), Num("1"))
                                            )
                                        ),
                                        App(App(Q("KingHorizontal.pivot"), V("c")), V("d"))
                                    ),
                                    App(
                                        App(
                                            Q("KingGrid.Edge"),
                                            Add(Add(Add(V("a"), Num("1")), Add(V("b"), Num("1"))), Num("1"))
                                        ),
                                        Add(Add(V("c"), Add(V("d"), Num("1"))), Num("1"))
                                    )
                                )
                            ),
                            Mul(
                                Num("6"),
                                Add(
                                    Add(
                                        Add(
                                            Add(
                                                Add(
                                                    App(
                                                        App(
                                                            App(Q("KingHorizontal.E"), Add(V("a"), V("b"))),
                                                            V("c")
                                                        ),
                                                        V("d")
                                                    ),
                                                    Power(Num("2"), Add(V("a"), V("b")))
                                                ),
                                                App(
                                                    App(
                                                        App(App(Q("KingHorizontal.P"), V("a")), V("b")),
                                                        V("c")
                                                    ),
                                                    V("d")
                                                )
                                            ),
                                            App(
                                                App(App(App(Q("KingHorizontal.P"), V("a")), V("b")), V("d")),
                                                V("c")
                                            )
                                        ),
                                        App(
                                            App(App(App(Q("KingHorizontal.Q"), V("a")), V("b")), V("c")),
                                            V("d")
                                        )
                                    ),
                                    App(App(App(App(Q("KingHorizontal.Q"), V("a")), V("b")), V("d")), V("c"))
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula14() =>
        All(
            "M",
            Q("Nat"),
            Eq(
                App(App(Q("KingDifference.N_H"), Num("1")), V("M")),
                Mul(Num("6"), Mul(V("M"), Power(Num("2"), V("M"))))
            )
        );

    private static Formula Formula15() =>
        All(
            "m",
            Q("Nat"),
            Eq(
                App(
                    Q("KingDifference.N_e"),
                    Typed(
                        App(App(Q("KingGrid.Edge.H"), Num("0")), Typed(Num("0"), App(Q("Fin"), Num("1")))),
                        App(App(Q("KingGrid.Edge"), Add(Add(V("m"), Num("1")), Num("1"))), Num("2"))
                    )
                ),
                Mul(Num("6"), Power(Num("2"), V("m")))
            )
        );

    private static Formula Formula16() =>
        All(
            "m",
            Q("Nat"),
            Eq(
                App(
                    Q("Nat.card"),
                    Subtype(
                        "b",
                        App(App(Q("KingHorizontal.BoundaryData"), V("m")), Num("1")),
                        App(
                            App(Q("KingHorizontal.BoundaryValid"), Typed(Num("0"), App(Q("Fin"), Num("1")))),
                            V("b")
                        )
                    )
                ),
                Mul(Num("6"), Power(Num("2"), V("m")))
            )
        );

    private static Formula Formula17() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                Eq(
                    App(
                        Q("KingDifference.N_e"),
                        Typed(
                            App(
                                App(
                                    Q("KingGrid.Edge.H"),
                                    App(
                                        App(Q("KingHorizontal.cut_row"), Add(V("a"), Num("1"))),
                                        Add(V("b"), Num("1"))
                                    )
                                ),
                                Typed(Num("0"), App(Q("Fin"), Num("1")))
                            ),
                            App(
                                App(
                                    Q("KingGrid.Edge"),
                                    Add(Add(Add(V("a"), Num("1")), Add(V("b"), Num("1"))), Num("1"))
                                ),
                                Num("2")
                            )
                        )
                    ),
                    Mul(Num("36"), Power(Num("2"), Add(V("a"), V("b"))))
                )
            )
        );

    private static Formula Formula18() =>
        All(
            "p",
            Q("Nat"),
            Eq(
                App(App(Q("KingDifference.N_H"), Add(V("p"), Num("1"))), Num("1")),
                Mul(Num("6"), Mul(Add(Mul(Num("3"), V("p")), Num("2")), Power(Num("2"), V("p"))))
            )
        );

    private static Formula Formula19() =>
        All(
            "c",
            Q("Nat"),
            All(
                "d",
                Q("Nat"),
                Eq(
                    App(
                        Q("KingDifference.N_e"),
                        Typed(
                            App(
                                App(Q("KingGrid.Edge.H"), Typed(Num("1"), App(Q("Fin"), Num("3")))),
                                App(App(Q("KingHorizontal.pivot"), V("c")), V("d"))
                            ),
                            App(
                                App(Q("KingGrid.Edge"), Num("3")),
                                Add(Add(V("c"), Add(V("d"), Num("1"))), Num("1"))
                            )
                        )
                    ),
                    Mul(
                        Num("6"),
                        Add(
                            Add(
                                Add(Power(Num("2"), Add(V("c"), V("d"))), Power(Num("2"), V("c"))),
                                Power(Num("2"), V("d"))
                            ),
                            Num("3")
                        )
                    )
                )
            )
        );

    private static Formula Formula20() =>
        All(
            "q",
            Q("Nat"),
            Eq(
                Add(App(App(Q("KingDifference.N_H"), Num("2")), Add(V("q"), Num("1"))), Num("54")),
                Mul(
                    Num("6"),
                    Add(
                        Mul(Add(V("q"), Num("13")), Power(Num("2"), V("q"))),
                        Mul(Num("3"), Add(V("q"), Num("2")))
                    )
                )
            )
        );

    private static Formula Formula21() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "d",
                    Q("Nat"),
                    Imp(
                        Lt(Num("0"), Add(V("a"), V("b"))),
                        Imp(
                            Lt(Num("0"), V("d")),
                            Eq(
                                Add(
                                    Add(
                                        Add(
                                            Add(
                                                Add(
                                                    Add(
                                                        App(
                                                            App(
                                                                App(
                                                                    Q("KingHorizontal.E"),
                                                                    Add(V("a"), V("b"))
                                                                ),
                                                                Num("0")
                                                            ),
                                                            V("d")
                                                        ),
                                                        Power(Num("2"), Add(V("a"), V("b")))
                                                    ),
                                                    App(
                                                        App(
                                                            App(App(Q("KingHorizontal.P"), V("a")), V("b")),
                                                            Num("0")
                                                        ),
                                                        V("d")
                                                    )
                                                ),
                                                App(
                                                    App(
                                                        App(App(Q("KingHorizontal.P"), V("a")), V("b")),
                                                        V("d")
                                                    ),
                                                    Num("0")
                                                )
                                            ),
                                            App(
                                                App(App(App(Q("KingHorizontal.Q"), V("a")), V("b")), Num("0")),
                                                V("d")
                                            )
                                        ),
                                        App(
                                            App(App(App(Q("KingHorizontal.Q"), V("a")), V("b")), V("d")),
                                            Num("0")
                                        )
                                    ),
                                    Num("2")
                                ),
                                Add(
                                    Add(
                                        Add(
                                            Power(Num("2"), Add(Add(V("a"), V("b")), Num("1"))),
                                            Power(Num("2"), Add(V("d"), Num("1")))
                                        ),
                                        Power(Num("2"), Add(V("a"), Num("1")))
                                    ),
                                    Power(Num("2"), Add(V("b"), Num("1")))
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula22() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "c",
                    Q("Nat"),
                    All(
                        "d",
                        Q("Nat"),
                        Imp(
                            Lt(Num("0"), Add(V("a"), V("b"))),
                            Imp(
                                Lt(Num("0"), V("c")),
                                Imp(
                                    Lt(Num("0"), V("d")),
                                    Eq(
                                        Add(
                                            Add(
                                                Add(
                                                    Add(
                                                        Add(
                                                            App(
                                                                App(
                                                                    App(
                                                                        Q("KingHorizontal.E"),
                                                                        Add(V("a"), V("b"))
                                                                    ),
                                                                    V("c")
                                                                ),
                                                                V("d")
                                                            ),
                                                            Power(Num("2"), Add(V("a"), V("b")))
                                                        ),
                                                        App(
                                                            App(
                                                                App(
                                                                    App(Q("KingHorizontal.P"), V("a")),
                                                                    V("b")
                                                                ),
                                                                V("c")
                                                            ),
                                                            V("d")
                                                        )
                                                    ),
                                                    App(
                                                        App(
                                                            App(App(Q("KingHorizontal.P"), V("a")), V("b")),
                                                            V("d")
                                                        ),
                                                        V("c")
                                                    )
                                                ),
                                                App(
                                                    App(
                                                        App(App(Q("KingHorizontal.Q"), V("a")), V("b")),
                                                        V("c")
                                                    ),
                                                    V("d")
                                                )
                                            ),
                                            App(
                                                App(App(App(Q("KingHorizontal.Q"), V("a")), V("b")), V("d")),
                                                V("c")
                                            )
                                        ),
                                        Add(
                                            Add(
                                                Add(
                                                    Power(Num("2"), Add(Add(V("a"), V("b")), Num("1"))),
                                                    Power(Num("2"), V("c"))
                                                ),
                                                Power(Num("2"), V("d"))
                                            ),
                                            Mul(
                                                Num("2"),
                                                Add(
                                                    Call("ite", Eq(V("a"), Num("0")), Num("1"), Num("0")),
                                                    Call("ite", Eq(V("b"), Num("0")), Num("1"), Num("0"))
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula23() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "q",
                    Q("Nat"),
                    Imp(
                        Lt(Num("0"), Add(V("a"), V("b"))),
                        Eq(
                            Add(
                                SumOver(
                                    "s",
                                    App(Q("Fin"), Add(V("q"), Num("2"))),
                                    App(
                                        Q("KingDifference.N_e"),
                                        Typed(
                                            App(
                                                App(
                                                    Q("KingGrid.Edge.H"),
                                                    App(
                                                        App(
                                                            Q("KingHorizontal.cut_row"),
                                                            Add(V("a"), Num("1"))
                                                        ),
                                                        Add(V("b"), Num("1"))
                                                    )
                                                ),
                                                V("s")
                                            ),
                                            App(
                                                App(
                                                    Q("KingGrid.Edge"),
                                                    Add(
                                                        Add(Add(V("a"), Num("1")), Add(V("b"), Num("1"))),
                                                        Num("1")
                                                    )
                                                ),
                                                Add(Add(V("q"), Num("2")), Num("1"))
                                            )
                                        )
                                    )
                                ),
                                Num("48")
                            ),
                            Mul(
                                Num("6"),
                                Add(
                                    Add(
                                        Add(
                                            Add(
                                                Mul(
                                                    Add(V("q"), Num("2")),
                                                    Power(Num("2"), Add(Add(V("a"), V("b")), Num("1")))
                                                ),
                                                Mul(Num("3"), Power(Num("2"), Add(V("q"), Num("2"))))
                                            ),
                                            Power(Num("2"), Add(V("a"), Num("2")))
                                        ),
                                        Power(Num("2"), Add(V("b"), Num("2")))
                                    ),
                                    Mul(
                                        Mul(Num("2"), V("q")),
                                        Add(
                                            Call("ite", Eq(V("a"), Num("0")), Num("1"), Num("0")),
                                            Call("ite", Eq(V("b"), Num("0")), Num("1"), Num("0"))
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula24() =>
        All(
            "m",
            Q("Nat"),
            All(
                "q",
                Q("Nat"),
                Imp(
                    Lt(Num("0"), V("m")),
                    Eq(
                        Add(
                            Add(
                                SumOver(
                                    "s",
                                    App(Q("Fin"), Add(V("q"), Num("2"))),
                                    App(
                                        Q("KingDifference.N_e"),
                                        Typed(
                                            App(
                                                App(
                                                    Q("KingGrid.Edge.H"),
                                                    Typed(Num("0"), App(Q("Fin"), Add(V("m"), Num("2"))))
                                                ),
                                                V("s")
                                            ),
                                            App(
                                                App(Q("KingGrid.Edge"), Add(V("m"), Num("2"))),
                                                Add(Add(V("q"), Num("2")), Num("1"))
                                            )
                                        )
                                    )
                                ),
                                Mul(Num("12"), Add(V("q"), Num("2")))
                            ),
                            Num("12")
                        ),
                        Mul(
                            Num("6"),
                            Add(
                                Mul(Add(V("q"), Num("2")), Power(Num("2"), V("m"))),
                                Power(Num("2"), Add(V("q"), Num("3")))
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula25() =>
        All(
            "t",
            Q("Nat"),
            All(
                "q",
                Q("Nat"),
                Eq(
                    Add(
                        App(App(Q("KingDifference.N_H"), Add(V("t"), Num("3"))), Add(V("q"), Num("2"))),
                        Mul(Num("6"), Add(Mul(Num("8"), Add(V("t"), Num("4"))), Num("4")))
                    ),
                    Mul(
                        Num("6"),
                        Add(
                            Mul(
                                Add(Mul(Add(V("t"), Num("4")), Add(V("q"), Num("2"))), Num("8")),
                                Power(Num("2"), Add(V("t"), Num("2")))
                            ),
                            Mul(Add(Mul(Num("3"), V("t")), Num("10")), Power(Num("2"), Add(V("q"), Num("2"))))
                        )
                    )
                )
            )
        );

    private static Formula V(string s) => F.Id(s);
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string s)
    {
        var parts = s.Split('_');
        Formula Word(string p) => Seq(p.Select(ch => ch >= '0' && ch <= '9'
            ? Num(new string(new[] { ch })) : V(new string(new[] { ch }))).ToArray());
        Formula result = Word(parts[^1]);
        for (var i = parts.Length - 2; i >= 0; --i)
            result = Seq(Word(parts[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Subtype(string x, Formula t, Formula b) =>
        Seq(OpenBrace, V(x), Colon, Sp, t, Sp, Slash, Slash, Sp, Parenthesized(b), CloseBrace);
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string x, Formula t, Formula b) =>
        Seq(Sum, Underscore, Grp(Seq(V(x), Colon, Sp, t)), Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Set(params Formula[] a) => new Formula.SetLiteral([.. a]);

}
