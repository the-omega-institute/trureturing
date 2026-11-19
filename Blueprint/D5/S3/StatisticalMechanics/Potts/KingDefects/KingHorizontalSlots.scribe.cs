using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class KingHorizontalSlotsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalSlots.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: KingHorizontalSlots"),
        Blocks(
            Node("InteriorSlots", "InteriorSlots", Formula0(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Two valid boundary assignments share every horizontal slot except the defective position. Their special ordered pairs may differ."),
            Node("interior_slot_equiv", "interior slot equiv", Formula1(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Cut at the defective row and express the two resulting boundary fields as compatible slot assignments."),
            Node("OrdinaryAlphabet", "OrdinaryAlphabet", Formula2(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "An ordinary vertical colour is nonzero and differs from the sum of the special ordered pair."),
            Node("InteriorAlphabet", "InteriorAlphabet", Formula3(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "A shared horizontal colour excludes zero, the two relevant special colours and every value of both ordinary vertical words."),
            Node("interior_count_alphabets", "interior count alphabets", Formula4(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "After choosing the two special pairs and the ordinary vertical words, the shared horizontal positions vary independently in their allowed alphabets."),
            Node("word_support", "word support", Formula5(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The support is the image of the entire finite index set under the Boolean word."),
            Node("word_support_empty", "word support empty", Formula6(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "A Boolean word has empty image exactly when its index set is empty."),
            Node("word_support_singleton", "word support singleton", Formula7(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "A nonempty Boolean word has singleton support exactly when it is the corresponding constant word."),
            Node("word_support_full", "word support full", Formula8(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "A nonempty Boolean word has both values exactly when it is neither constant false nor constant true."),
            Node("support_weight", "support weight", Formula9(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "An empty word has empty support. A nonempty word has one realization for either singleton support, no realization for empty support, and 2 raised to n minus two realizations for full support. Subtraction is natural subtraction."),
            Node("word_support_card", "word support card", Formula10(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The number of Boolean words with a fixed support is its support weight."),
            Node("sum_by_support", "sum by support", Formula11(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Apply Fintype.sum_fiberwise' to word_support, then use word_support_card to weight each support by its number of realizations."),
            Node("ordinary_value", "ordinary value", Formula12(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "False chooses the first entry and true the second entry of the ordered pair."),
            Node("ordinary_value_valid", "ordinary value valid", Formula13(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Either selected entry is nonzero and differs from the sum of the two distinct nonzero entries."),
            Node("SupportAlphabet", "SupportAlphabet", Formula14(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Replace the vertical words by their supports while retaining all exclusions on a horizontal colour."),
            Node("pair_support_count", "pair support count", Formula15(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Sum over the two Boolean supports. Their word multiplicities multiply the independent left and right horizontal alphabet powers."),
            Node("pair_count_support", "pair count support", Formula16(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Transport ordinary vertical words to Boolean words and group the sum by their two supports."))));

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
                    "M",
                    Q("Nat"),
                    All(
                        "s",
                        App(Q("Fin"), V("M")),
                        Eq(
                            Call("KingHorizontal.InteriorSlots", V("a"), V("b"), V("M"), V("s")),
                            Subtype(
                                "q",
                                Product(
                                    Subtype(
                                        "u",
                                        App(App(Q("KingHorizontal.BoundaryData"), V("a")), V("M")),
                                        App(App(Q("KingHorizontal.BoundaryValid"), V("s")), V("u"))
                                    ),
                                    Subtype(
                                        "l",
                                        App(App(Q("KingHorizontal.BoundaryData"), V("b")), V("M")),
                                        App(App(Q("KingHorizontal.BoundaryValid"), V("s")), V("l"))
                                    )
                                ),
                                All(
                                    "j",
                                    App(Q("Fin"), V("M")),
                                    Imp(
                                        Ne(V("j"), V("s")),
                                        Eq(
                                            App(
                                                Call(
                                                    "KingHorizontal.BoundaryData.h",
                                                    Call("Subtype.val", Call("Prod.fst", V("q")))
                                                ),
                                                V("j")
                                            ),
                                            App(
                                                Call(
                                                    "KingHorizontal.BoundaryData.h",
                                                    Call("Subtype.val", Call("Prod.snd", V("q")))
                                                ),
                                                V("j")
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

    private static Formula Formula1() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "M",
                    Q("Nat"),
                    All(
                        "s",
                        App(Q("Fin"), V("M")),
                        And(
                            Typed(
                                Call("KingHorizontal.interior_slot_equiv", V("a"), V("b"), V("M"), V("s")),
                                Equivalence(
                                    Subtype(
                                        "t",
                                        App(
                                            App(
                                                Q("KingDifference.DiffField"),
                                                Add(Add(V("a"), Num("1")), Add(V("b"), Num("1")))
                                            ),
                                            V("M")
                                        ),
                                        App(
                                            App(
                                                Q("KingDifference.RawAdmissible"),
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
                                                )
                                            ),
                                            V("t")
                                        )
                                    ),
                                    App(
                                        App(
                                            App(App(Q("KingHorizontal.InteriorSlots"), V("a")), V("b")),
                                            V("M")
                                        ),
                                        V("s")
                                    )
                                )
                            ),
                            All(
                                "t",
                                Subtype(
                                    "t",
                                    App(
                                        App(
                                            Q("KingDifference.DiffField"),
                                            Add(Add(V("a"), Num("1")), Add(V("b"), Num("1")))
                                        ),
                                        V("M")
                                    ),
                                    App(
                                        App(
                                            Q("KingDifference.RawAdmissible"),
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
                                            )
                                        ),
                                        V("t")
                                    )
                                ),
                                And(
                                    Eq(
                                        Call(
                                            "Subtype.val",
                                            Call(
                                                "Prod.fst",
                                                Call(
                                                    "Subtype.val",
                                                    App(
                                                        Call(
                                                            "KingHorizontal.interior_slot_equiv",
                                                            V("a"),
                                                            V("b"),
                                                            V("M"),
                                                            V("s")
                                                        ),
                                                        V("t")
                                                    )
                                                )
                                            )
                                        ),
                                        Call(
                                            "KingHorizontal.boundary_extract",
                                            V("s"),
                                            Call(
                                                "KingHorizontal.row_reflect",
                                                Call(
                                                    "Prod.fst",
                                                    Call(
                                                        "Subtype.val",
                                                        App(
                                                            Call(
                                                                "KingHorizontal.horizontal_cut_equiv",
                                                                Add(V("a"), Num("1")),
                                                                Add(V("b"), Num("1")),
                                                                V("M"),
                                                                V("s")
                                                            ),
                                                            V("t")
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    ),
                                    Eq(
                                        Call(
                                            "Subtype.val",
                                            Call(
                                                "Prod.snd",
                                                Call(
                                                    "Subtype.val",
                                                    App(
                                                        Call(
                                                            "KingHorizontal.interior_slot_equiv",
                                                            V("a"),
                                                            V("b"),
                                                            V("M"),
                                                            V("s")
                                                        ),
                                                        V("t")
                                                    )
                                                )
                                            )
                                        ),
                                        Call(
                                            "KingHorizontal.boundary_extract",
                                            V("s"),
                                            Call(
                                                "Prod.snd",
                                                Call(
                                                    "Subtype.val",
                                                    App(
                                                        Call(
                                                            "KingHorizontal.horizontal_cut_equiv",
                                                            Add(V("a"), Num("1")),
                                                            Add(V("b"), Num("1")),
                                                            V("M"),
                                                            V("s")
                                                        ),
                                                        V("t")
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

    private static Formula Formula2() =>
        All(
            "x",
            Q("KingDifference.NZPair"),
            Eq(
                Call("KingHorizontal.OrdinaryAlphabet", V("x")),
                Subtype(
                    "v",
                    Q("KingDifference.K"),
                    And(
                        Ne(V("v"), Num("0")),
                        Ne(
                            V("v"),
                            Add(
                                Call("Prod.fst", Call("Subtype.val", V("x"))),
                                Call("Prod.snd", Call("Subtype.val", V("x")))
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula3() =>
        All(
            "a",
            Q("Nat"),
            All(
                "b",
                Q("Nat"),
                All(
                    "x",
                    Q("KingDifference.NZPair"),
                    All(
                        "y",
                        Q("KingDifference.NZPair"),
                        All(
                            "u",
                            Arrow(App(Q("Fin"), V("a")), App(Q("KingHorizontal.OrdinaryAlphabet"), V("x"))),
                            All(
                                "v",
                                Arrow(
                                    App(Q("Fin"), V("b")),
                                    App(Q("KingHorizontal.OrdinaryAlphabet"), V("y"))
                                ),
                                All(
                                    "p",
                                    Q("KingDifference.K"),
                                    All(
                                        "q",
                                        Q("KingDifference.K"),
                                        Eq(
                                            Call(
                                                "KingHorizontal.InteriorAlphabet",
                                                V("x"),
                                                V("y"),
                                                V("u"),
                                                V("v"),
                                                V("p"),
                                                V("q")
                                            ),
                                            Subtype(
                                                "h",
                                                Q("KingDifference.K"),
                                                And(
                                                    Ne(V("h"), Num("0")),
                                                    And(
                                                        Ne(V("h"), V("p")),
                                                        And(
                                                            Ne(V("h"), V("q")),
                                                            And(
                                                                All(
                                                                    "i",
                                                                    App(Q("Fin"), V("a")),
                                                                    Ne(
                                                                        V("h"),
                                                                        Call(
                                                                            "Subtype.val",
                                                                            App(V("u"), V("i"))
                                                                        )
                                                                    )
                                                                ),
                                                                All(
                                                                    "i",
                                                                    App(Q("Fin"), V("b")),
                                                                    Ne(
                                                                        V("h"),
                                                                        Call(
                                                                            "Subtype.val",
                                                                            App(V("v"), V("i"))
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
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula4() =>
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
                                    SumOver(
                                        "u",
                                        Arrow(
                                            App(Q("Fin"), V("a")),
                                            App(Q("KingHorizontal.OrdinaryAlphabet"), V("x"))
                                        ),
                                        SumOver(
                                            "v",
                                            Arrow(
                                                App(Q("Fin"), V("b")),
                                                App(Q("KingHorizontal.OrdinaryAlphabet"), V("y"))
                                            ),
                                            Mul(
                                                Power(
                                                    App(
                                                        Q("Nat.card"),
                                                        App(
                                                            App(
                                                                App(
                                                                    App(
                                                                        App(
                                                                            App(
                                                                                Q(
                                                                                    "KingHorizontal.InteriorAlphabet"
                                                                                ),
                                                                                V("x")
                                                                            ),
                                                                            V("y")
                                                                        ),
                                                                        V("u")
                                                                    ),
                                                                    V("v")
                                                                ),
                                                                Call("Prod.fst", Call("Subtype.val", V("x")))
                                                            ),
                                                            Call("Prod.fst", Call("Subtype.val", V("y")))
                                                        )
                                                    ),
                                                    V("c")
                                                ),
                                                Power(
                                                    App(
                                                        Q("Nat.card"),
                                                        App(
                                                            App(
                                                                App(
                                                                    App(
                                                                        App(
                                                                            App(
                                                                                Q(
                                                                                    "KingHorizontal.InteriorAlphabet"
                                                                                ),
                                                                                V("x")
                                                                            ),
                                                                            V("y")
                                                                        ),
                                                                        V("u")
                                                                    ),
                                                                    V("v")
                                                                ),
                                                                Call("Prod.snd", Call("Subtype.val", V("x")))
                                                            ),
                                                            Call("Prod.snd", Call("Subtype.val", V("y")))
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
            )
        );

    private static Formula Formula5() =>
        All(
            "n",
            Q("Nat"),
            All(
                "u",
                Arrow(App(Q("Fin"), V("n")), Q("Bool")),
                Eq(
                    Call("KingHorizontal.word_support", V("u")),
                    App(
                        App(Q("Finset.image"), V("u")),
                        Typed(Q("Finset.univ"), App(Q("Finset"), App(Q("Fin"), V("n"))))
                    )
                )
            )
        );

    private static Formula Formula6() =>
        All(
            "n",
            Q("Nat"),
            All(
                "u",
                Arrow(App(Q("Fin"), V("n")), Q("Bool")),
                Iff(
                    Eq(App(Q("KingHorizontal.word_support"), V("u")), Q("Finset.empty")),
                    Eq(V("n"), Num("0"))
                )
            )
        );

    private static Formula Formula7() =>
        All(
            "n",
            Q("Nat"),
            Imp(
                Lt(Num("0"), V("n")),
                All(
                    "u",
                    Arrow(App(Q("Fin"), V("n")), Q("Bool")),
                    All(
                        "b",
                        Q("Bool"),
                        Iff(
                            Eq(App(Q("KingHorizontal.word_support"), V("u")), Set(V("b"))),
                            Eq(V("u"), Call("Function.const", App(Q("Fin"), V("n")), V("b")))
                        )
                    )
                )
            )
        );

    private static Formula Formula8() =>
        All(
            "n",
            Q("Nat"),
            Imp(
                Lt(Num("0"), V("n")),
                All(
                    "u",
                    Arrow(App(Q("Fin"), V("n")), Q("Bool")),
                    Iff(
                        Eq(App(Q("KingHorizontal.word_support"), V("u")), Q("Finset.univ")),
                        And(
                            Ne(V("u"), Call("Function.const", App(Q("Fin"), V("n")), Q("Bool.false"))),
                            Ne(V("u"), Call("Function.const", App(Q("Fin"), V("n")), Q("Bool.true")))
                        )
                    )
                )
            )
        );

    private static Formula Formula9() =>
        All(
            "n",
            Q("Nat"),
            All(
                "S",
                App(Q("Finset"), Q("Bool")),
                Eq(
                    Call("KingHorizontal.support_weight", V("n"), V("S")),
                    Call(
                        "ite",
                        Eq(V("n"), Num("0")),
                        Call("ite", Eq(V("S"), Q("Finset.empty")), Num("1"), Num("0")),
                        Call(
                            "ite",
                            Eq(V("S"), Q("Finset.empty")),
                            Num("0"),
                            Call(
                                "ite",
                                Or(Eq(V("S"), Set(Q("Bool.false"))), Eq(V("S"), Set(Q("Bool.true")))),
                                Num("1"),
                                Sub(Power(Num("2"), V("n")), Num("2"))
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula10() =>
        All(
            "n",
            Q("Nat"),
            All(
                "S",
                App(Q("Finset"), Q("Bool")),
                Eq(
                    App(
                        Q("Nat.card"),
                        Subtype(
                            "u",
                            Arrow(App(Q("Fin"), V("n")), Q("Bool")),
                            Eq(App(Q("KingHorizontal.word_support"), V("u")), V("S"))
                        )
                    ),
                    App(App(Q("KingHorizontal.support_weight"), V("n")), V("S"))
                )
            )
        );

    private static Formula Formula11() =>
        All(
            "n",
            Q("Nat"),
            All(
                "f",
                Arrow(App(Q("Finset"), Q("Bool")), Q("Nat")),
                Eq(
                    SumOver(
                        "u",
                        Arrow(App(Q("Fin"), V("n")), Q("Bool")),
                        App(V("f"), App(Q("KingHorizontal.word_support"), V("u")))
                    ),
                    SumOver(
                        "S",
                        App(Q("Finset"), Q("Bool")),
                        Mul(App(App(Q("KingHorizontal.support_weight"), V("n")), V("S")), App(V("f"), V("S")))
                    )
                )
            )
        );

    private static Formula Formula12() =>
        All(
            "x",
            Q("KingDifference.NZPair"),
            All(
                "b",
                Q("Bool"),
                Eq(
                    Call("KingHorizontal.ordinary_value", V("x"), V("b")),
                    Call(
                        "ite",
                        V("b"),
                        Call("Prod.snd", Call("Subtype.val", V("x"))),
                        Call("Prod.fst", Call("Subtype.val", V("x")))
                    )
                )
            )
        );

    private static Formula Formula13() =>
        All(
            "x",
            Q("KingDifference.NZPair"),
            All(
                "b",
                Q("Bool"),
                And(
                    Ne(App(App(Q("KingHorizontal.ordinary_value"), V("x")), V("b")), Num("0")),
                    Ne(
                        App(App(Q("KingHorizontal.ordinary_value"), V("x")), V("b")),
                        Add(
                            Call("Prod.fst", Call("Subtype.val", V("x"))),
                            Call("Prod.snd", Call("Subtype.val", V("x")))
                        )
                    )
                )
            )
        );

    private static Formula Formula14() =>
        All(
            "x",
            Q("KingDifference.NZPair"),
            All(
                "y",
                Q("KingDifference.NZPair"),
                All(
                    "S",
                    App(Q("Finset"), Q("Bool")),
                    All(
                        "T",
                        App(Q("Finset"), Q("Bool")),
                        All(
                            "p",
                            Q("KingDifference.K"),
                            All(
                                "q",
                                Q("KingDifference.K"),
                                Eq(
                                    Call(
                                        "KingHorizontal.SupportAlphabet",
                                        V("x"),
                                        V("y"),
                                        V("S"),
                                        V("T"),
                                        V("p"),
                                        V("q")
                                    ),
                                    Subtype(
                                        "h",
                                        Q("KingDifference.K"),
                                        And(
                                            Ne(V("h"), Num("0")),
                                            And(
                                                Ne(V("h"), V("p")),
                                                And(
                                                    Ne(V("h"), V("q")),
                                                    And(
                                                        All(
                                                            "z",
                                                            Q("Bool"),
                                                            Imp(
                                                                Member(V("z"), V("S")),
                                                                Ne(
                                                                    V("h"),
                                                                    App(
                                                                        App(
                                                                            Q("KingHorizontal.ordinary_value"),
                                                                            V("x")
                                                                        ),
                                                                        V("z")
                                                                    )
                                                                )
                                                            )
                                                        ),
                                                        All(
                                                            "z",
                                                            Q("Bool"),
                                                            Imp(
                                                                Member(V("z"), V("T")),
                                                                Ne(
                                                                    V("h"),
                                                                    App(
                                                                        App(
                                                                            Q("KingHorizontal.ordinary_value"),
                                                                            V("y")
                                                                        ),
                                                                        V("z")
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
                        )
                    )
                )
            )
        );

    private static Formula Formula15() =>
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
                                "y",
                                Q("KingDifference.NZPair"),
                                Eq(
                                    Call(
                                        "KingHorizontal.pair_support_count",
                                        V("a"),
                                        V("b"),
                                        V("c"),
                                        V("d"),
                                        V("x"),
                                        V("y")
                                    ),
                                    SumOver(
                                        "S",
                                        App(Q("Finset"), Q("Bool")),
                                        SumOver(
                                            "T",
                                            App(Q("Finset"), Q("Bool")),
                                            Mul(
                                                Mul(
                                                    Mul(
                                                        App(
                                                            App(Q("KingHorizontal.support_weight"), V("a")),
                                                            V("S")
                                                        ),
                                                        App(
                                                            App(Q("KingHorizontal.support_weight"), V("b")),
                                                            V("T")
                                                        )
                                                    ),
                                                    Power(
                                                        App(
                                                            Q("Nat.card"),
                                                            App(
                                                                App(
                                                                    App(
                                                                        App(
                                                                            App(
                                                                                App(
                                                                                    Q(
                                                                                        "KingHorizontal.SupportAlphabet"
                                                                                    ),
                                                                                    V("x")
                                                                                ),
                                                                                V("y")
                                                                            ),
                                                                            V("S")
                                                                        ),
                                                                        V("T")
                                                                    ),
                                                                    Call(
                                                                        "Prod.fst",
                                                                        Call("Subtype.val", V("x"))
                                                                    )
                                                                ),
                                                                Call("Prod.fst", Call("Subtype.val", V("y")))
                                                            )
                                                        ),
                                                        V("c")
                                                    )
                                                ),
                                                Power(
                                                    App(
                                                        Q("Nat.card"),
                                                        App(
                                                            App(
                                                                App(
                                                                    App(
                                                                        App(
                                                                            App(
                                                                                Q(
                                                                                    "KingHorizontal.SupportAlphabet"
                                                                                ),
                                                                                V("x")
                                                                            ),
                                                                            V("y")
                                                                        ),
                                                                        V("S")
                                                                    ),
                                                                    V("T")
                                                                ),
                                                                Call("Prod.snd", Call("Subtype.val", V("x")))
                                                            ),
                                                            Call("Prod.snd", Call("Subtype.val", V("y")))
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
            )
        );

    private static Formula Formula16() =>
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
                                "y",
                                Q("KingDifference.NZPair"),
                                Eq(
                                    SumOver(
                                        "u",
                                        Arrow(
                                            App(Q("Fin"), V("a")),
                                            App(Q("KingHorizontal.OrdinaryAlphabet"), V("x"))
                                        ),
                                        SumOver(
                                            "v",
                                            Arrow(
                                                App(Q("Fin"), V("b")),
                                                App(Q("KingHorizontal.OrdinaryAlphabet"), V("y"))
                                            ),
                                            Mul(
                                                Power(
                                                    App(
                                                        Q("Nat.card"),
                                                        App(
                                                            App(
                                                                App(
                                                                    App(
                                                                        App(
                                                                            App(
                                                                                Q(
                                                                                    "KingHorizontal.InteriorAlphabet"
                                                                                ),
                                                                                V("x")
                                                                            ),
                                                                            V("y")
                                                                        ),
                                                                        V("u")
                                                                    ),
                                                                    V("v")
                                                                ),
                                                                Call("Prod.fst", Call("Subtype.val", V("x")))
                                                            ),
                                                            Call("Prod.fst", Call("Subtype.val", V("y")))
                                                        )
                                                    ),
                                                    V("c")
                                                ),
                                                Power(
                                                    App(
                                                        Q("Nat.card"),
                                                        App(
                                                            App(
                                                                App(
                                                                    App(
                                                                        App(
                                                                            App(
                                                                                Q(
                                                                                    "KingHorizontal.InteriorAlphabet"
                                                                                ),
                                                                                V("x")
                                                                            ),
                                                                            V("y")
                                                                        ),
                                                                        V("u")
                                                                    ),
                                                                    V("v")
                                                                ),
                                                                Call("Prod.snd", Call("Subtype.val", V("x")))
                                                            ),
                                                            Call("Prod.snd", Call("Subtype.val", V("y")))
                                                        )
                                                    ),
                                                    V("d")
                                                )
                                            )
                                        )
                                    ),
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
    private static Formula Equivalence(Formula a, Formula b) => Call("Equiv", a, b);
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
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));

    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Set(params Formula[] a) => new Formula.SetLiteral([.. a]);

}
