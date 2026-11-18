using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class KingHorizontalBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/KingHorizontalBoundary.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: KingHorizontalBoundary"),
        Blocks(
            Node("BoundaryData", "BoundaryData", Formula0(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The record contains two special colours p and q, a horizontal word h of length M and an ordinary vertical word v of length m."),
            Node("BoundaryValid", "BoundaryValid", Formula1(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The special colours are distinct and nonzero. The pivot is their sum; all slots are nonzero. Left and right slots exclude p and q respectively, and every horizontal slot differs from every ordinary vertical slot."),
            Node("boundary_build", "boundary build", Formula2(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Fin.cons prepends the exceptional row to each field. Function.update sets horizontal position s to zero. The first vertical step uses p through column s and q afterwards; Function.const supplies the constant tails."),
            Node("boundary_extract", "boundary extract", Formula3(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The special colours are the two vertical values adjacent to s on the first step. The horizontal word comes from row one and the ordinary vertical word from column zero."),
            Node("boundary_h", "boundary h", Formula4(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Every nondefective horizontal slot is constant through the rows, while the selected bond has value zero."),
            Node("boundary_slot_equiv", "boundary slot equiv", Formula5(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Extraction and filling identify admissible top-boundary fields with valid boundary data."),
            Node("BoundaryWords", "BoundaryWords", Formula6(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The vertical word and the left and right horizontal words are Boolean. A nonconstant vertical word forces both side words to be constantly true."),
            Node("boundary_words_zero_card", "boundary words zero card", Formula7(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "With no ordinary vertical positions, the two horizontal words are independent binary words."),
            Node("boundary_words_pos_card", "boundary words pos card", Formula8(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "For positive m, partition according to the two constant vertical words and the remaining vertical words."),
            Node("pivot", "pivot", Formula9(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The pivot has natural value c in a row of c + d + 1 positions."),
            Node("boundary_count_zero", "boundary count zero", Formula10(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Six choices of the special ordered pair multiply the binary choices on the two horizontal sides."),
            Node("boundary_count_pos", "boundary count pos", Formula11(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "For positive m, the two constant vertical cases and the remaining vertical cases give the three powers of two."),
            Node("horizontal_count_row_reflect", "horizontal count row reflect", Formula12(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Row reflection gives a bijection of admissible fields at the two reflected horizontal bonds."),
            Node("E", "E", Formula13(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The empty ordinary vertical word leaves two independent horizontal words. For positive m the two constant vertical words and the nonconstant words give the second branch. Subtraction is natural subtraction."),
            Node("boundary_count", "boundary count", Formula14(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The boundary-field count is six times its Boolean-word count, including an empty ordinary vertical word."),
            Node("boundary_count_at", "boundary count at", Formula15(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The column index determines the left side length, and natural subtraction gives the right side length."),
            Node("boundary_rows_count", "boundary rows count", Formula16(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The same count holds on either boundary row by row reflection."),
            Node("row_reflect", "row reflect", Formula17(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Reverse both finite row indices; column indices and colours are unchanged."),
            Node("row_reflect_raw", "row reflect raw", Formula18(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Reversing the row indices preserves compatibility and sends the unique zero bond to its reflected row."),
            Node("row_reflect_equiv", "row reflect equiv", Formula19(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Row reversal is its own inverse on admissible difference fields."),
            Node("boundary_bottom_slot_equiv", "boundary bottom slot equiv", Formula20(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Reflect an admissible bottom-boundary field to the top boundary, then extract its valid boundary data."),
            Node("cut_row", "cut row", Formula21(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The shared row is pivot A B, with natural value A in a rectangle with A + B vertical steps."),
            Node("CutFields", "CutFields", Formula22(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The two half-fields have defects at their common row and agree on every horizontal value there, including the zero at s."),
            Node("horizontal_cut_equiv", "horizontal cut equiv", Formula23(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Restrict above and below the selected row. The row embeddings top_row and bottom_row use Fin.castLE and Fin.natAdd, respectively. The inverse uses Fin.append to join the vertical tuples, and Fin.append with Fin.init of the upper horizontal tuple joins the horizontal tuples, retaining the lower copy of the shared row."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Formula0() =>
        All(
            "m",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                And(
                    And(
                        And(
                            And(
                                Typed(
                                    Q("KingHorizontal.BoundaryData.mk"),
                                    Arrow(
                                        Q("KingDifference.K"),
                                        Arrow(
                                            Q("KingDifference.K"),
                                            Arrow(
                                                Arrow(App(Q("Fin"), V("M")), Q("KingDifference.K")),
                                                Arrow(
                                                    Arrow(App(Q("Fin"), V("m")), Q("KingDifference.K")),
                                                    Call("KingHorizontal.BoundaryData", V("m"), V("M"))
                                                )
                                            )
                                        )
                                    )
                                ),
                                Typed(
                                    Q("KingHorizontal.BoundaryData.p"),
                                    Arrow(
                                        Call("KingHorizontal.BoundaryData", V("m"), V("M")),
                                        Q("KingDifference.K")
                                    )
                                )
                            ),
                            Typed(
                                Q("KingHorizontal.BoundaryData.q"),
                                Arrow(
                                    Call("KingHorizontal.BoundaryData", V("m"), V("M")),
                                    Q("KingDifference.K")
                                )
                            )
                        ),
                        Typed(
                            Q("KingHorizontal.BoundaryData.h"),
                            Arrow(
                                Call("KingHorizontal.BoundaryData", V("m"), V("M")),
                                Arrow(App(Q("Fin"), V("M")), Q("KingDifference.K"))
                            )
                        )
                    ),
                    Typed(
                        Q("KingHorizontal.BoundaryData.v"),
                        Arrow(
                            Call("KingHorizontal.BoundaryData", V("m"), V("M")),
                            Arrow(App(Q("Fin"), V("m")), Q("KingDifference.K"))
                        )
                    )
                )
            )
        );

    private static Formula Formula1() =>
        All(
            "m",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "s",
                    App(Q("Fin"), V("M")),
                    All(
                        "b",
                        App(App(Q("KingHorizontal.BoundaryData"), V("m")), V("M")),
                        Iff(
                            Call("KingHorizontal.BoundaryValid", V("s"), V("b")),
                            And(
                                Ne(Call("KingHorizontal.BoundaryData.p", V("b")), Num("0")),
                                And(
                                    Ne(Call("KingHorizontal.BoundaryData.q", V("b")), Num("0")),
                                    And(
                                        Ne(
                                            Call("KingHorizontal.BoundaryData.p", V("b")),
                                            Call("KingHorizontal.BoundaryData.q", V("b"))
                                        ),
                                        And(
                                            Eq(
                                                App(Call("KingHorizontal.BoundaryData.h", V("b")), V("s")),
                                                Add(
                                                    Call("KingHorizontal.BoundaryData.p", V("b")),
                                                    Call("KingHorizontal.BoundaryData.q", V("b"))
                                                )
                                            ),
                                            And(
                                                All(
                                                    "j",
                                                    App(Q("Fin"), V("M")),
                                                    Ne(
                                                        App(
                                                            Call("KingHorizontal.BoundaryData.h", V("b")),
                                                            V("j")
                                                        ),
                                                        Num("0")
                                                    )
                                                ),
                                                And(
                                                    All(
                                                        "i",
                                                        App(Q("Fin"), V("m")),
                                                        Ne(
                                                            App(
                                                                Call("KingHorizontal.BoundaryData.v", V("b")),
                                                                V("i")
                                                            ),
                                                            Num("0")
                                                        )
                                                    ),
                                                    And(
                                                        All(
                                                            "j",
                                                            App(Q("Fin"), V("M")),
                                                            Imp(
                                                                Lt(V("j"), V("s")),
                                                                Ne(
                                                                    App(
                                                                        Call(
                                                                            "KingHorizontal.BoundaryData.h",
                                                                            V("b")
                                                                        ),
                                                                        V("j")
                                                                    ),
                                                                    Call(
                                                                        "KingHorizontal.BoundaryData.p",
                                                                        V("b")
                                                                    )
                                                                )
                                                            )
                                                        ),
                                                        And(
                                                            All(
                                                                "j",
                                                                App(Q("Fin"), V("M")),
                                                                Imp(
                                                                    Lt(V("s"), V("j")),
                                                                    Ne(
                                                                        App(
                                                                            Call(
                                                                                "KingHorizontal.BoundaryData.h",
                                                                                V("b")
                                                                            ),
                                                                            V("j")
                                                                        ),
                                                                        Call(
                                                                            "KingHorizontal.BoundaryData.q",
                                                                            V("b")
                                                                        )
                                                                    )
                                                                )
                                                            ),
                                                            All(
                                                                "i",
                                                                App(Q("Fin"), V("m")),
                                                                All(
                                                                    "j",
                                                                    App(Q("Fin"), V("M")),
                                                                    Ne(
                                                                        App(
                                                                            Call(
                                                                                "KingHorizontal.BoundaryData.h",
                                                                                V("b")
                                                                            ),
                                                                            V("j")
                                                                        ),
                                                                        App(
                                                                            Call(
                                                                                "KingHorizontal.BoundaryData.v",
                                                                                V("b")
                                                                            ),
                                                                            V("i")
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

    private static Formula Formula2()
    {
        var field = Call("KingHorizontal.boundary_build", V("s"), V("b"));
        var horizontal = Call("KingHorizontal.BoundaryData.h", V("b"));
        var vertical = Call("KingHorizontal.BoundaryData.v", V("b"));
        var first = Lam("j", Call("Fin", Add(V("M"), Num("1"))),
            Call("ite", Leq(Call("Fin.val", V("j")), Call("Fin.val", V("s"))),
                Call("KingHorizontal.BoundaryData.p", V("b")),
                Call("KingHorizontal.BoundaryData.q", V("b"))));
        var tail = Lam("i", Call("Fin", V("m")),
            Call("Function.const", Call("Fin", Add(V("M"), Num("1"))), App(vertical, V("i"))));
        return All("m", Q("Nat"), All("M", Q("Nat"),
            All("s", Call("Fin", V("M")),
                All("b", Call("KingHorizontal.BoundaryData", V("m"), V("M")),
                    And(
                        Eq(Call("KingDifference.DiffField.h", field),
                            Call("Fin.cons", Call("Function.update", horizontal, V("s"), Num("0")),
                                Call("Function.const", Call("Fin", Add(V("m"), Num("1"))), horizontal))),
                        Eq(Call("KingDifference.DiffField.v", field), Call("Fin.cons", first, tail)))))));
    }

    private static Formula Formula3() =>
        All(
            "m",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "s",
                    App(Q("Fin"), V("M")),
                    All(
                        "t",
                        App(App(Q("KingDifference.DiffField"), Add(V("m"), Num("1"))), V("M")),
                        And(
                            Eq(
                                Call(
                                    "KingHorizontal.BoundaryData.p",
                                    App(App(Q("KingHorizontal.boundary_extract"), V("s")), V("t"))
                                ),
                                App(
                                    App(Call("KingDifference.DiffField.v", V("t")), Num("0")),
                                    App(Q("Fin.castSucc"), V("s"))
                                )
                            ),
                            And(
                                Eq(
                                    Call(
                                        "KingHorizontal.BoundaryData.q",
                                        App(App(Q("KingHorizontal.boundary_extract"), V("s")), V("t"))
                                    ),
                                    App(
                                        App(Call("KingDifference.DiffField.v", V("t")), Num("0")),
                                        App(Q("Fin.succ"), V("s"))
                                    )
                                ),
                                And(
                                    All(
                                        "j",
                                        App(Q("Fin"), V("M")),
                                        Eq(
                                            App(
                                                Call(
                                                    "KingHorizontal.BoundaryData.h",
                                                    App(
                                                        App(Q("KingHorizontal.boundary_extract"), V("s")),
                                                        V("t")
                                                    )
                                                ),
                                                V("j")
                                            ),
                                            App(
                                                App(Call("KingDifference.DiffField.h", V("t")), Num("1")),
                                                V("j")
                                            )
                                        )
                                    ),
                                    All(
                                        "i",
                                        App(Q("Fin"), V("m")),
                                        Eq(
                                            App(
                                                Call(
                                                    "KingHorizontal.BoundaryData.v",
                                                    App(
                                                        App(Q("KingHorizontal.boundary_extract"), V("s")),
                                                        V("t")
                                                    )
                                                ),
                                                V("i")
                                            ),
                                            App(
                                                App(
                                                    Call("KingDifference.DiffField.v", V("t")),
                                                    App(Q("Fin.succ"), V("i"))
                                                ),
                                                Num("0")
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
            "m",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "s",
                    App(Q("Fin"), V("M")),
                    All(
                        "t",
                        App(App(Q("KingDifference.DiffField"), Add(V("m"), Num("1"))), V("M")),
                        Imp(
                            App(
                                App(
                                    Q("KingDifference.RawAdmissible"),
                                    App(App(Q("KingGrid.Edge.H"), Num("0")), V("s"))
                                ),
                                V("t")
                            ),
                            All(
                                "i",
                                App(Q("Fin"), Add(Add(V("m"), Num("1")), Num("1"))),
                                All(
                                    "j",
                                    App(Q("Fin"), V("M")),
                                    Eq(
                                        App(App(Call("KingDifference.DiffField.h", V("t")), V("i")), V("j")),
                                        Call(
                                            "ite",
                                            And(Eq(V("i"), Num("0")), Eq(V("j"), V("s"))),
                                            Num("0"),
                                            App(
                                                App(Call("KingDifference.DiffField.h", V("t")), Num("1")),
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

    private static Formula Formula5() =>
        All(
            "m",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "s",
                    App(Q("Fin"), V("M")),
                    And(
                        Typed(
                            Call("KingHorizontal.boundary_slot_equiv", V("m"), V("M"), V("s")),
                            Equivalence(
                                Subtype(
                                    "t",
                                    App(App(Q("KingDifference.DiffField"), Add(V("m"), Num("1"))), V("M")),
                                    App(
                                        App(
                                            Q("KingDifference.RawAdmissible"),
                                            App(App(Q("KingGrid.Edge.H"), Num("0")), V("s"))
                                        ),
                                        V("t")
                                    )
                                ),
                                Subtype(
                                    "b",
                                    App(App(Q("KingHorizontal.BoundaryData"), V("m")), V("M")),
                                    App(App(Q("KingHorizontal.BoundaryValid"), V("s")), V("b"))
                                )
                            )
                        ),
                        All(
                            "t",
                            Subtype(
                                "t",
                                App(App(Q("KingDifference.DiffField"), Add(V("m"), Num("1"))), V("M")),
                                App(
                                    App(
                                        Q("KingDifference.RawAdmissible"),
                                        App(App(Q("KingGrid.Edge.H"), Num("0")), V("s"))
                                    ),
                                    V("t")
                                )
                            ),
                            Eq(
                                Call(
                                    "Subtype.val",
                                    App(
                                        Call("KingHorizontal.boundary_slot_equiv", V("m"), V("M"), V("s")),
                                        V("t")
                                    )
                                ),
                                Call("KingHorizontal.boundary_extract", V("s"), Call("Subtype.val", V("t")))
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula6() =>
        All(
            "m",
            Q("Nat"),
            All(
                "c",
                Q("Nat"),
                All(
                    "d",
                    Q("Nat"),
                    Eq(
                        Call("KingHorizontal.BoundaryWords", V("m"), V("c"), V("d")),
                        Subtype(
                            "w",
                            Product(
                                Arrow(App(Q("Fin"), V("m")), Q("Bool")),
                                Product(
                                    Arrow(App(Q("Fin"), V("c")), Q("Bool")),
                                    Arrow(App(Q("Fin"), V("d")), Q("Bool"))
                                )
                            ),
                            And(
                                Imp(
                                    Ne(
                                        Call("Prod.fst", V("w")),
                                        App(App(Q("Function.const"), App(Q("Fin"), V("m"))), Q("Bool.false"))
                                    ),
                                    Eq(
                                        Call("Prod.fst", Call("Prod.snd", V("w"))),
                                        App(App(Q("Function.const"), App(Q("Fin"), V("c"))), Q("Bool.true"))
                                    )
                                ),
                                Imp(
                                    Ne(
                                        Call("Prod.fst", V("w")),
                                        App(App(Q("Function.const"), App(Q("Fin"), V("m"))), Q("Bool.true"))
                                    ),
                                    Eq(
                                        Call("Prod.snd", Call("Prod.snd", V("w"))),
                                        App(App(Q("Function.const"), App(Q("Fin"), V("d"))), Q("Bool.true"))
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula7() =>
        All(
            "c",
            Q("Nat"),
            All(
                "d",
                Q("Nat"),
                Eq(
                    App(
                        Q("Nat.card"),
                        App(App(App(Q("KingHorizontal.BoundaryWords"), Num("0")), V("c")), V("d"))
                    ),
                    Power(Num("2"), Add(V("c"), V("d")))
                )
            )
        );

    private static Formula Formula8() =>
        All(
            "m",
            Q("Nat"),
            All(
                "c",
                Q("Nat"),
                All(
                    "d",
                    Q("Nat"),
                    Imp(
                        Lt(Num("0"), V("m")),
                        Eq(
                            Add(
                                App(
                                    Q("Nat.card"),
                                    App(App(App(Q("KingHorizontal.BoundaryWords"), V("m")), V("c")), V("d"))
                                ),
                                Num("2")
                            ),
                            Add(
                                Add(Power(Num("2"), V("m")), Power(Num("2"), V("c"))),
                                Power(Num("2"), V("d"))
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula9() =>
        All(
            "c",
            Q("Nat"),
            All(
                "d",
                Q("Nat"),
                And(
                    Typed(
                        Call("KingHorizontal.pivot", V("c"), V("d")),
                        App(Q("Fin"), Add(V("c"), Add(V("d"), Num("1"))))
                    ),
                    Eq(Call("Fin.val", Call("KingHorizontal.pivot", V("c"), V("d"))), V("c"))
                )
            )
        );

    private static Formula Formula10() =>
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
                                App(Q("KingGrid.Edge.H"), Num("0")),
                                App(App(Q("KingHorizontal.pivot"), V("c")), V("d"))
                            ),
                            App(
                                App(Q("KingGrid.Edge"), Num("2")),
                                Add(Add(V("c"), Add(V("d"), Num("1"))), Num("1"))
                            )
                        )
                    ),
                    Mul(Num("6"), Power(Num("2"), Add(V("c"), V("d"))))
                )
            )
        );

    private static Formula Formula11() =>
        All(
            "m",
            Q("Nat"),
            All(
                "c",
                Q("Nat"),
                All(
                    "d",
                    Q("Nat"),
                    Imp(
                        Lt(Num("0"), V("m")),
                        Eq(
                            Add(
                                App(
                                    Q("KingDifference.N_e"),
                                    Typed(
                                        App(
                                            App(Q("KingGrid.Edge.H"), Num("0")),
                                            App(App(Q("KingHorizontal.pivot"), V("c")), V("d"))
                                        ),
                                        App(
                                            App(Q("KingGrid.Edge"), Add(Add(V("m"), Num("1")), Num("1"))),
                                            Add(Add(V("c"), Add(V("d"), Num("1"))), Num("1"))
                                        )
                                    )
                                ),
                                Num("12")
                            ),
                            Mul(
                                Num("6"),
                                Add(
                                    Add(Power(Num("2"), V("m")), Power(Num("2"), V("c"))),
                                    Power(Num("2"), V("d"))
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula12() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "i",
                    App(Q("Fin"), Add(V("N"), Num("1"))),
                    All(
                        "j",
                        App(Q("Fin"), V("M")),
                        Eq(
                            App(
                                Q("KingDifference.N_e"),
                                Typed(
                                    App(App(Q("KingGrid.Edge.H"), Call("Fin.rev", V("i"))), V("j")),
                                    App(App(Q("KingGrid.Edge"), Add(V("N"), Num("1"))), Add(V("M"), Num("1")))
                                )
                            ),
                            App(Q("KingDifference.N_e"), App(App(Q("KingGrid.Edge.H"), V("i")), V("j")))
                        )
                    )
                )
            )
        );

    private static Formula Formula13() =>
        All(
            "m",
            Q("Nat"),
            All(
                "c",
                Q("Nat"),
                All(
                    "d",
                    Q("Nat"),
                    Eq(
                        Call("KingHorizontal.E", V("m"), V("c"), V("d")),
                        Call(
                            "ite",
                            Eq(V("m"), Num("0")),
                            Power(Num("2"), Add(V("c"), V("d"))),
                            Sub(
                                Add(
                                    Add(Power(Num("2"), V("m")), Power(Num("2"), V("c"))),
                                    Power(Num("2"), V("d"))
                                ),
                                Num("2")
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula14() =>
        All(
            "m",
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
                                    App(Q("KingGrid.Edge.H"), Num("0")),
                                    App(App(Q("KingHorizontal.pivot"), V("c")), V("d"))
                                ),
                                App(
                                    App(Q("KingGrid.Edge"), Add(Add(V("m"), Num("1")), Num("1"))),
                                    Add(Add(V("c"), Add(V("d"), Num("1"))), Num("1"))
                                )
                            )
                        ),
                        Mul(Num("6"), App(App(App(Q("KingHorizontal.E"), V("m")), V("c")), V("d")))
                    )
                )
            )
        );

    private static Formula Formula15() =>
        All(
            "m",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "s",
                    App(Q("Fin"), V("M")),
                    Eq(
                        App(
                            Q("KingDifference.N_e"),
                            Typed(
                                App(App(Q("KingGrid.Edge.H"), Num("0")), V("s")),
                                App(
                                    App(Q("KingGrid.Edge"), Add(Add(V("m"), Num("1")), Num("1"))),
                                    Add(V("M"), Num("1"))
                                )
                            )
                        ),
                        Mul(
                            Num("6"),
                            App(
                                App(App(Q("KingHorizontal.E"), V("m")), Call("Fin.val", V("s"))),
                                Sub(Sub(V("M"), Num("1")), Call("Fin.val", V("s")))
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula16() =>
        All(
            "m",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "r",
                    App(Q("Fin"), Add(Add(V("m"), Num("1")), Num("1"))),
                    All(
                        "s",
                        App(Q("Fin"), V("M")),
                        Imp(
                            Or(Eq(V("r"), Num("0")), Eq(V("r"), App(Q("Fin.last"), Add(V("m"), Num("1"))))),
                            Eq(
                                App(
                                    Q("KingDifference.N_e"),
                                    Typed(
                                        App(App(Q("KingGrid.Edge.H"), V("r")), V("s")),
                                        App(
                                            App(Q("KingGrid.Edge"), Add(Add(V("m"), Num("1")), Num("1"))),
                                            Add(V("M"), Num("1"))
                                        )
                                    )
                                ),
                                Mul(
                                    Num("6"),
                                    App(
                                        App(App(Q("KingHorizontal.E"), V("m")), Call("Fin.val", V("s"))),
                                        Sub(Sub(V("M"), Num("1")), Call("Fin.val", V("s")))
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula17() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "t",
                    App(App(Q("KingDifference.DiffField"), V("N")), V("M")),
                    And(
                        All(
                            "i",
                            App(Q("Fin"), Add(V("N"), Num("1"))),
                            All(
                                "j",
                                App(Q("Fin"), V("M")),
                                Eq(
                                    App(
                                        App(
                                            Call(
                                                "KingDifference.DiffField.h",
                                                App(Q("KingHorizontal.row_reflect"), V("t"))
                                            ),
                                            V("i")
                                        ),
                                        V("j")
                                    ),
                                    App(
                                        App(
                                            Call("KingDifference.DiffField.h", V("t")),
                                            App(Q("Fin.rev"), V("i"))
                                        ),
                                        V("j")
                                    )
                                )
                            )
                        ),
                        All(
                            "i",
                            App(Q("Fin"), V("N")),
                            All(
                                "j",
                                App(Q("Fin"), Add(V("M"), Num("1"))),
                                Eq(
                                    App(
                                        App(
                                            Call(
                                                "KingDifference.DiffField.v",
                                                App(Q("KingHorizontal.row_reflect"), V("t"))
                                            ),
                                            V("i")
                                        ),
                                        V("j")
                                    ),
                                    App(
                                        App(
                                            Call("KingDifference.DiffField.v", V("t")),
                                            App(Q("Fin.rev"), V("i"))
                                        ),
                                        V("j")
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula18() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "r",
                    App(Q("Fin"), Add(V("N"), Num("1"))),
                    All(
                        "s",
                        App(Q("Fin"), V("M")),
                        All(
                            "t",
                            App(App(Q("KingDifference.DiffField"), V("N")), V("M")),
                            Imp(
                                App(
                                    App(
                                        Q("KingDifference.RawAdmissible"),
                                        App(App(Q("KingGrid.Edge.H"), V("r")), V("s"))
                                    ),
                                    V("t")
                                ),
                                App(
                                    App(
                                        Q("KingDifference.RawAdmissible"),
                                        App(App(Q("KingGrid.Edge.H"), Call("Fin.rev", V("r"))), V("s"))
                                    ),
                                    App(Q("KingHorizontal.row_reflect"), V("t"))
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula19() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "r",
                    App(Q("Fin"), Add(V("N"), Num("1"))),
                    All(
                        "s",
                        App(Q("Fin"), V("M")),
                        And(
                            Typed(
                                Call("KingHorizontal.row_reflect_equiv", V("r"), V("s")),
                                Equivalence(
                                    Subtype(
                                        "t",
                                        App(App(Q("KingDifference.DiffField"), V("N")), V("M")),
                                        App(
                                            App(
                                                Q("KingDifference.RawAdmissible"),
                                                App(App(Q("KingGrid.Edge.H"), V("r")), V("s"))
                                            ),
                                            V("t")
                                        )
                                    ),
                                    Subtype(
                                        "t",
                                        App(App(Q("KingDifference.DiffField"), V("N")), V("M")),
                                        App(
                                            App(
                                                Q("KingDifference.RawAdmissible"),
                                                App(
                                                    App(Q("KingGrid.Edge.H"), Call("Fin.rev", V("r"))),
                                                    V("s")
                                                )
                                            ),
                                            V("t")
                                        )
                                    )
                                )
                            ),
                            All(
                                "t",
                                Subtype(
                                    "t",
                                    App(App(Q("KingDifference.DiffField"), V("N")), V("M")),
                                    App(
                                        App(
                                            Q("KingDifference.RawAdmissible"),
                                            App(App(Q("KingGrid.Edge.H"), V("r")), V("s"))
                                        ),
                                        V("t")
                                    )
                                ),
                                Eq(
                                    Call(
                                        "Subtype.val",
                                        App(Call("KingHorizontal.row_reflect_equiv", V("r"), V("s")), V("t"))
                                    ),
                                    Call("KingHorizontal.row_reflect", Call("Subtype.val", V("t")))
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula20() =>
        All(
            "m",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "s",
                    App(Q("Fin"), V("M")),
                    And(
                        Typed(
                            Call("KingHorizontal.boundary_bottom_slot_equiv", V("m"), V("M"), V("s")),
                            Equivalence(
                                Subtype(
                                    "t",
                                    App(App(Q("KingDifference.DiffField"), Add(V("m"), Num("1"))), V("M")),
                                    App(
                                        App(
                                            Q("KingDifference.RawAdmissible"),
                                            App(
                                                App(
                                                    Q("KingGrid.Edge.H"),
                                                    App(Q("Fin.last"), Add(V("m"), Num("1")))
                                                ),
                                                V("s")
                                            )
                                        ),
                                        V("t")
                                    )
                                ),
                                Subtype(
                                    "b",
                                    App(App(Q("KingHorizontal.BoundaryData"), V("m")), V("M")),
                                    App(App(Q("KingHorizontal.BoundaryValid"), V("s")), V("b"))
                                )
                            )
                        ),
                        All(
                            "t",
                            Subtype(
                                "t",
                                App(App(Q("KingDifference.DiffField"), Add(V("m"), Num("1"))), V("M")),
                                App(
                                    App(
                                        Q("KingDifference.RawAdmissible"),
                                        App(
                                            App(
                                                Q("KingGrid.Edge.H"),
                                                App(Q("Fin.last"), Add(V("m"), Num("1")))
                                            ),
                                            V("s")
                                        )
                                    ),
                                    V("t")
                                )
                            ),
                            Eq(
                                Call(
                                    "Subtype.val",
                                    App(
                                        Call(
                                            "KingHorizontal.boundary_bottom_slot_equiv",
                                            V("m"),
                                            V("M"),
                                            V("s")
                                        ),
                                        V("t")
                                    )
                                ),
                                Call(
                                    "KingHorizontal.boundary_extract",
                                    V("s"),
                                    Call("KingHorizontal.row_reflect", Call("Subtype.val", V("t")))
                                )
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula21() =>
        All(
            "A",
            Q("Nat"),
            All(
                "B",
                Q("Nat"),
                And(
                    Typed(
                        Call("KingHorizontal.cut_row", V("A"), V("B")),
                        App(Q("Fin"), Add(Add(V("A"), V("B")), Num("1")))
                    ),
                    And(
                        Eq(Call("KingHorizontal.cut_row", V("A"), V("B")),
                            Call("KingHorizontal.pivot", V("A"), V("B"))),
                        Eq(Call("Fin.val", Call("KingHorizontal.cut_row", V("A"), V("B"))), V("A")))
                )
            )
        );

    private static Formula Formula22() =>
        All(
            "A",
            Q("Nat"),
            All(
                "B",
                Q("Nat"),
                All(
                    "M",
                    Q("Nat"),
                    All(
                        "s",
                        App(Q("Fin"), V("M")),
                        Eq(
                            Call("KingHorizontal.CutFields", V("A"), V("B"), V("M"), V("s")),
                            Subtype(
                                "q",
                                Product(
                                    App(App(Q("KingDifference.DiffField"), V("A")), V("M")),
                                    App(App(Q("KingDifference.DiffField"), V("B")), V("M"))
                                ),
                                And(
                                    App(
                                        App(
                                            Q("KingDifference.RawAdmissible"),
                                            App(App(Q("KingGrid.Edge.H"), App(Q("Fin.last"), V("A"))), V("s"))
                                        ),
                                        Call("Prod.fst", V("q"))
                                    ),
                                    And(
                                        App(
                                            App(
                                                Q("KingDifference.RawAdmissible"),
                                                App(App(Q("KingGrid.Edge.H"), Num("0")), V("s"))
                                            ),
                                            Call("Prod.snd", V("q"))
                                        ),
                                        All(
                                            "j",
                                            App(Q("Fin"), V("M")),
                                            Eq(
                                                App(
                                                    App(
                                                        Call(
                                                            "KingDifference.DiffField.h",
                                                            Call("Prod.fst", V("q"))
                                                        ),
                                                        App(Q("Fin.last"), V("A"))
                                                    ),
                                                    V("j")
                                                ),
                                                App(
                                                    App(
                                                        Call(
                                                            "KingDifference.DiffField.h",
                                                            Call("Prod.snd", V("q"))
                                                        ),
                                                        Num("0")
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
            )
        );

    private static Formula Formula23() => And(Formula23Restrictions(), Formula23Inverse());

    private static Formula Formula23Restrictions() =>
        All(
            "A",
            Q("Nat"),
            All(
                "B",
                Q("Nat"),
                All(
                    "M",
                    Q("Nat"),
                    All(
                        "s",
                        App(Q("Fin"), V("M")),
                        And(
                            Typed(
                                Call("KingHorizontal.horizontal_cut_equiv", V("A"), V("B"), V("M"), V("s")),
                                Equivalence(
                                    Subtype(
                                        "t",
                                        App(App(Q("KingDifference.DiffField"), Add(V("A"), V("B"))), V("M")),
                                        App(
                                            App(
                                                Q("KingDifference.RawAdmissible"),
                                                App(
                                                    App(
                                                        Q("KingGrid.Edge.H"),
                                                        App(App(Q("KingHorizontal.cut_row"), V("A")), V("B"))
                                                    ),
                                                    V("s")
                                                )
                                            ),
                                            V("t")
                                        )
                                    ),
                                    App(
                                        App(App(App(Q("KingHorizontal.CutFields"), V("A")), V("B")), V("M")),
                                        V("s")
                                    )
                                )
                            ),
                            All(
                                "t",
                                Subtype(
                                    "t",
                                    App(App(Q("KingDifference.DiffField"), Add(V("A"), V("B"))), V("M")),
                                    App(
                                        App(
                                            Q("KingDifference.RawAdmissible"),
                                            App(
                                                App(
                                                    Q("KingGrid.Edge.H"),
                                                    App(App(Q("KingHorizontal.cut_row"), V("A")), V("B"))
                                                ),
                                                V("s")
                                            )
                                        ),
                                        V("t")
                                    )
                                ),
                                And(
                                    All(
                                        "i",
                                        App(Q("Fin"), Add(V("A"), Num("1"))),
                                        All(
                                            "k",
                                            App(Q("Fin"), Add(Add(V("A"), V("B")), Num("1"))),
                                            All(
                                                "j",
                                                App(Q("Fin"), V("M")),
                                                Imp(
                                                    Eq(Call("Fin.val", V("k")), Call("Fin.val", V("i"))),
                                                    Eq(
                                                        Call(
                                                            "KingDifference.DiffField.h",
                                                            Call(
                                                                "Prod.fst",
                                                                Call(
                                                                    "Subtype.val",
                                                                    App(
                                                                        Call(
                                                                            "KingHorizontal.horizontal_cut_equiv",
                                                                            V("A"),
                                                                            V("B"),
                                                                            V("M"),
                                                                            V("s")
                                                                        ),
                                                                        V("t")
                                                                    )
                                                                )
                                                            ),
                                                            V("i"),
                                                            V("j")
                                                        ),
                                                        Call(
                                                            "KingDifference.DiffField.h",
                                                            Call("Subtype.val", V("t")),
                                                            V("k"),
                                                            V("j")
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    ),
                                    And(
                                        All(
                                            "i",
                                            App(Q("Fin"), V("A")),
                                            All(
                                                "k",
                                                App(Q("Fin"), Add(V("A"), V("B"))),
                                                All(
                                                    "j",
                                                    App(Q("Fin"), Add(V("M"), Num("1"))),
                                                    Imp(
                                                        Eq(Call("Fin.val", V("k")), Call("Fin.val", V("i"))),
                                                        Eq(
                                                            Call(
                                                                "KingDifference.DiffField.v",
                                                                Call(
                                                                    "Prod.fst",
                                                                    Call(
                                                                        "Subtype.val",
                                                                        App(
                                                                            Call(
                                                                                "KingHorizontal.horizontal_cut_equiv",
                                                                                V("A"),
                                                                                V("B"),
                                                                                V("M"),
                                                                                V("s")
                                                                            ),
                                                                            V("t")
                                                                        )
                                                                    )
                                                                ),
                                                                V("i"),
                                                                V("j")
                                                            ),
                                                            Call(
                                                                "KingDifference.DiffField.v",
                                                                Call("Subtype.val", V("t")),
                                                                V("k"),
                                                                V("j")
                                                            )
                                                        )
                                                    )
                                                )
                                            )
                                        ),
                                        And(
                                            All(
                                                "i",
                                                App(Q("Fin"), Add(V("B"), Num("1"))),
                                                All(
                                                    "k",
                                                    App(Q("Fin"), Add(Add(V("A"), V("B")), Num("1"))),
                                                    All(
                                                        "j",
                                                        App(Q("Fin"), V("M")),
                                                        Imp(
                                                            Eq(
                                                                Call("Fin.val", V("k")),
                                                                Add(V("A"), Call("Fin.val", V("i")))
                                                            ),
                                                            Eq(
                                                                Call(
                                                                    "KingDifference.DiffField.h",
                                                                    Call(
                                                                        "Prod.snd",
                                                                        Call(
                                                                            "Subtype.val",
                                                                            App(
                                                                                Call(
                                                                                    "KingHorizontal.horizontal_cut_equiv",
                                                                                    V("A"),
                                                                                    V("B"),
                                                                                    V("M"),
                                                                                    V("s")
                                                                                ),
                                                                                V("t")
                                                                            )
                                                                        )
                                                                    ),
                                                                    V("i"),
                                                                    V("j")
                                                                ),
                                                                Call(
                                                                    "KingDifference.DiffField.h",
                                                                    Call("Subtype.val", V("t")),
                                                                    V("k"),
                                                                    V("j")
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                            ),
                                            All(
                                                "i",
                                                App(Q("Fin"), V("B")),
                                                All(
                                                    "k",
                                                    App(Q("Fin"), Add(V("A"), V("B"))),
                                                    All(
                                                        "j",
                                                        App(Q("Fin"), Add(V("M"), Num("1"))),
                                                        Imp(
                                                            Eq(
                                                                Call("Fin.val", V("k")),
                                                                Add(V("A"), Call("Fin.val", V("i")))
                                                            ),
                                                            Eq(
                                                                Call(
                                                                    "KingDifference.DiffField.v",
                                                                    Call(
                                                                        "Prod.snd",
                                                                        Call(
                                                                            "Subtype.val",
                                                                            App(
                                                                                Call(
                                                                                    "KingHorizontal.horizontal_cut_equiv",
                                                                                    V("A"),
                                                                                    V("B"),
                                                                                    V("M"),
                                                                                    V("s")
                                                                                ),
                                                                                V("t")
                                                                            )
                                                                        )
                                                                    ),
                                                                    V("i"),
                                                                    V("j")
                                                                ),
                                                                Call(
                                                                    "KingDifference.DiffField.v",
                                                                    Call("Subtype.val", V("t")),
                                                                    V("k"),
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
                            )
                        )
                    )
                )
            )
        );

    private static Formula Formula23Inverse()
    {
        var halves = Call("Subtype.val", V("q"));
        var upper = Call("Prod.fst", halves);
        var lower = Call("Prod.snd", halves);
        var joined = Call("Subtype.val",
            App(Call("Equiv.symm", Call("KingHorizontal.horizontal_cut_equiv", V("A"), V("B"), V("M"), V("s"))), V("q")));
        return All("A", Q("Nat"), All("B", Q("Nat"), All("M", Q("Nat"),
            All("s", Call("Fin", V("M")),
                All("q", Call("KingHorizontal.CutFields", V("A"), V("B"), V("M"), V("s")),
                    And(
                        Eq(Call("KingDifference.DiffField.h", joined),
                            Call("Fin.append", Call("Fin.init", Call("KingDifference.DiffField.h", upper)),
                                Call("KingDifference.DiffField.h", lower))),
                        Eq(Call("KingDifference.DiffField.v", joined),
                            Call("Fin.append", Call("KingDifference.DiffField.v", upper),
                                Call("KingDifference.DiffField.v", lower)))))))));
    }

    private static Formula Lam(string x, Formula t, Formula b) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(x), t), Sp, Mapsto, Sp, b));
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
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));

    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));

}
