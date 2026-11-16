using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class KingGridDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: KingGrid"),
        Blocks(
            Node("Cell", "Cells of the rectangle", Formula0(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "A cell consists of a row and a column, both indexed from zero."),
            Node("Edge", "The four kinds of king bonds", Formula1(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The four disjoint constructors list horizontal, vertical, descending diagonal and ascending diagonal bonds. Their parameters enumerate each undirected bond once."),
            Node("lo", "Left-slot endpoint index", Formula2(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "This endpoint uses QuandleMarkovColoring.leftSlot: its value is i.val in the longer finite interval."),
            Node("hi", "Right-slot endpoint index", Formula3(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "This endpoint uses QuandleMarkovColoring.rightSlot: its value is i.val+1 in the longer finite interval. The theorem QuandleMarkovColoring.slots_ne separates the two coordinates and hence the two endpoints of every king bond."),
            Node("end0", "First endpoints", Formula4(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "These endpoint formulas specify the two cells incident to each bond."),
            Node("end1", "Second endpoints", Formula5(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "These endpoint formulas specify the two cells incident to each bond."),
            Node("mono", "Monochromatic bonds", Formula6(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "A bond is monochromatic when its two endpoints have equal colours."),
            Node("OneDefect", "Exactly one monochromatic bond", Formula7(),
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "The predicate counts monochromatic bonds in all four directions and requires exactly one."),
            Node("DefectAt", "A prescribed defect", Formula8(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Exactly the selected bond is monochromatic."),
            Node("normal", "Row-major first appearances", Formula9(),
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "Flattening uses the ordinal i*k+j. The canonical word introduces smaller colour labels before larger labels, which is precisely row-major first-appearance order."),
            Node("L", "Labelled one-defect colourings", Formula10(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The finite filter ranges over all four-colour arrays. Colour names remain distinct."),
            Node("T", "Canonical one-defect colourings", Formula11(),
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "The finite filter ranges over all four-colour arrays. First appearances fix the colour names in increasing order."),
            Node("oneDefect_iff", "The unique defective bond", Formula12(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "A one-element set of monochromatic bonds is equivalent to a unique monochromatic bond."),
            Node("count_by_edge", "Partition by defective bond", Formula13(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Colourings with one defect are partitioned by the location of that defect."),
            Node("sum_edges", "Separate the four bond orientations", Formula14(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Summation over the bond type is the sum over its four constructors."),
            Node("transposeEdge", "Transpose bonds", Formula15(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Transposition exchanges horizontal and vertical bonds and preserves each diagonal orientation."),
            Node("reflectEdge", "Reflect columns", Formula16(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Column reflection reverses the column index and exchanges the two diagonal orientations."),
            Node("transpose", "Transpose a colouring", Formula17(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Transposition exchanges the two cell coordinates."),
            Node("transpose_mono", "Transposition preserves monochromatic bonds", Formula18(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The endpoints are transposed together, so equality of their colours is preserved."),
            Node("transposeDefectEquiv", "Transpose a prescribed defect", Formula19(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The map acts on colourings by the geometric symmetry and carries the selected defective bond along with it. Applying the symmetry twice gives the inverse."),
            Node("reflectDefectEquiv", "Reflect a prescribed defect", Formula20(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The map acts on colourings by the geometric symmetry and carries the selected defective bond along with it. Applying the symmetry twice gives the inverse."),
            Node("labelled_eq_twentyFour", "Twenty-four labelled colourings per canonical colouring", Formula21(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "For both side lengths at least two, each one-defect array uses at least three colours. A permutation of four colours fixing three is the identity. Each colour orbit therefore has twenty-four elements and one row-major canonical representative."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Formula0() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                Eq(Call("KingGrid.Cell", V("n"), V("k")), Product(Call("Fin", V("n")), Call("Fin", V("k"))))));

    private static Formula Formula1() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                And(
                    Typed(
                        Q("KingGrid.Edge.H"),
                        Arrow(
                            Call("Fin", V("n")),
                            Arrow(Call("Fin", Sub(V("k"), Num("1"))), Call("KingGrid.Edge", V("n"), V("k"))))),
                    And(
                        Typed(
                            Q("KingGrid.Edge.V"),
                            Arrow(
                                Call("Fin", Sub(V("n"), Num("1"))),
                                Arrow(Call("Fin", V("k")), Call("KingGrid.Edge", V("n"), V("k"))))),
                        And(
                            Typed(
                                Q("KingGrid.Edge.D"),
                                Arrow(
                                    Call("Fin", Sub(V("n"), Num("1"))),
                                    Arrow(
                                        Call("Fin", Sub(V("k"), Num("1"))),
                                        Call("KingGrid.Edge", V("n"), V("k"))))),
                            Typed(
                                Q("KingGrid.Edge.A"),
                                Arrow(
                                    Call("Fin", Sub(V("n"), Num("1"))),
                                    Arrow(
                                        Call("Fin", Sub(V("k"), Num("1"))),
                                        Call("KingGrid.Edge", V("n"), V("k"))))))))));

    private static Formula Formula2() =>
        All(
            "n",
            Q("Nat"),
            All("i", Call("Fin", Sub(V("n"), Num("1"))),
                Eq(Call("KingGrid.lo", V("i")), Call("QuandleMarkovColoring.leftSlot", V("i")))));

    private static Formula Formula3() =>
        All(
            "n",
            Q("Nat"),
            All(
                "i",
                Call("Fin", Sub(V("n"), Num("1"))),
                Eq(Call("KingGrid.hi", V("i")), Call("QuandleMarkovColoring.rightSlot", V("i")))));

    private static Formula Formula4() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                And(
                    All(
                        "i",
                        Call("Fin", V("n")),
                        All(
                            "j",
                            Call("Fin", Sub(V("k"), Num("1"))),
                            Eq(
                                Call("KingGrid.end0", Call("KingGrid.Edge.H", V("i"), V("j"))),
                                Pair(V("i"), Call("KingGrid.lo", V("j")))))),
                    And(
                        All(
                            "i",
                            Call("Fin", Sub(V("n"), Num("1"))),
                            All(
                                "j",
                                Call("Fin", V("k")),
                                Eq(
                                    Call("KingGrid.end0", Call("KingGrid.Edge.V", V("i"), V("j"))),
                                    Pair(Call("KingGrid.lo", V("i")), V("j"))))),
                        And(
                            All(
                                "i",
                                Call("Fin", Sub(V("n"), Num("1"))),
                                All(
                                    "j",
                                    Call("Fin", Sub(V("k"), Num("1"))),
                                    Eq(
                                        Call("KingGrid.end0", Call("KingGrid.Edge.D", V("i"), V("j"))),
                                        Pair(Call("KingGrid.lo", V("i")), Call("KingGrid.lo", V("j")))))),
                            All(
                                "i",
                                Call("Fin", Sub(V("n"), Num("1"))),
                                All(
                                    "j",
                                    Call("Fin", Sub(V("k"), Num("1"))),
                                    Eq(
                                        Call("KingGrid.end0", Call("KingGrid.Edge.A", V("i"), V("j"))),
                                        Pair(Call("KingGrid.lo", V("i")), Call("KingGrid.hi", V("j")))))))))));

    private static Formula Formula5() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                And(
                    All(
                        "i",
                        Call("Fin", V("n")),
                        All(
                            "j",
                            Call("Fin", Sub(V("k"), Num("1"))),
                            Eq(
                                Call("KingGrid.end1", Call("KingGrid.Edge.H", V("i"), V("j"))),
                                Pair(V("i"), Call("KingGrid.hi", V("j")))))),
                    And(
                        All(
                            "i",
                            Call("Fin", Sub(V("n"), Num("1"))),
                            All(
                                "j",
                                Call("Fin", V("k")),
                                Eq(
                                    Call("KingGrid.end1", Call("KingGrid.Edge.V", V("i"), V("j"))),
                                    Pair(Call("KingGrid.hi", V("i")), V("j"))))),
                        And(
                            All(
                                "i",
                                Call("Fin", Sub(V("n"), Num("1"))),
                                All(
                                    "j",
                                    Call("Fin", Sub(V("k"), Num("1"))),
                                    Eq(
                                        Call("KingGrid.end1", Call("KingGrid.Edge.D", V("i"), V("j"))),
                                        Pair(Call("KingGrid.hi", V("i")), Call("KingGrid.hi", V("j")))))),
                            All(
                                "i",
                                Call("Fin", Sub(V("n"), Num("1"))),
                                All(
                                    "j",
                                    Call("Fin", Sub(V("k"), Num("1"))),
                                    Eq(
                                        Call("KingGrid.end1", Call("KingGrid.Edge.A", V("i"), V("j"))),
                                        Pair(Call("KingGrid.hi", V("i")), Call("KingGrid.lo", V("j")))))))))));

    private static Formula Formula6() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                All(
                    "C",
                    Q("Type"),
                    All(
                        "f",
                        Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                        All(
                            "e",
                            Call("KingGrid.Edge", V("n"), V("k")),
                            Iff(
                                Call("KingGrid.mono", V("f"), V("e")),
                                Eq(
                                    App(V("f"), Call("KingGrid.end0", V("e"))),
                                    App(V("f"), Call("KingGrid.end1", V("e"))))))))));

    private static Formula Formula7() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                All(
                    "C",
                    Q("Type"),
                    Instance(
                        Call("DecidableEq", V("C")),
                        All(
                            "f",
                            Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                            Iff(
                                Call("KingGrid.OneDefect", V("f")),
                                Eq(
                                    Call(
                                        "Finset.card",
                                        Call(
                                            "Finset.filter",
                                            Fn(
                                                "e",
                                                Call("KingGrid.Edge", V("n"), V("k")),
                                                Call("KingGrid.mono", V("f"), V("e"))),
                                            Typed(
                                                Q("Finset.univ"),
                                                Call("Finset", Call("KingGrid.Edge", V("n"), V("k")))))),
                                    Num("1"))))))));

    private static Formula Formula8() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                All(
                    "C",
                    Q("Type"),
                    All(
                        "e",
                        Call("KingGrid.Edge", V("n"), V("k")),
                        All(
                            "f",
                            Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                            Iff(
                                Call("KingGrid.DefectAt", V("e"), V("f")),
                                All(
                                    "d",
                                    Call("KingGrid.Edge", V("n"), V("k")),
                                    Iff(Call("KingGrid.mono", V("f"), V("d")), Eq(V("d"), V("e"))))))))));

    private static Formula Formula9() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                All(
                    "f",
                    Arrow(Call("KingGrid.Cell", V("n"), V("k")), Call("Fin", Num("4"))),
                    Iff(
                        Call("KingGrid.normal", V("f")),
                        Call(
                            "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical",
                            Fn(
                                "i",
                                Call("Fin", Mul(V("n"), V("k"))),
                                App(V("f"), App(Call("Equiv.symm", Q("finProdFinEquiv")), V("i")))))))));

    private static Formula Formula10() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                Eq(
                    Call("KingGrid.L", V("n"), V("k")),
                    Call(
                        "Finset.card",
                        Call(
                            "Finset.filter",
                            Fn(
                                "f",
                                Arrow(Call("KingGrid.Cell", V("n"), V("k")), Call("Fin", Num("4"))),
                                Call("KingGrid.OneDefect", V("f"))),
                            Typed(
                                Q("Finset.univ"),
                                Call(
                                    "Finset",
                                    Arrow(Call("KingGrid.Cell", V("n"), V("k")), Call("Fin", Num("4"))))))))));

    private static Formula Formula11() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                Eq(
                    Call("KingGrid.T", V("n"), V("k")),
                    Call(
                        "Finset.card",
                        Call(
                            "Finset.filter",
                            Fn(
                                "f",
                                Arrow(Call("KingGrid.Cell", V("n"), V("k")), Call("Fin", Num("4"))),
                                And(Call("KingGrid.OneDefect", V("f")), Call("KingGrid.normal", V("f")))),
                            Typed(
                                Q("Finset.univ"),
                                Call(
                                    "Finset",
                                    Arrow(Call("KingGrid.Cell", V("n"), V("k")), Call("Fin", Num("4"))))))))));

    private static Formula Formula12() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                All(
                    "C",
                    Q("Type"),
                    Instance(
                        Call("DecidableEq", V("C")),
                        All(
                            "f",
                            Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                            Iff(
                                Call("KingGrid.OneDefect", V("f")),
                                Unique(
                                    "e",
                                    Call("KingGrid.Edge", V("n"), V("k")),
                                    Call("KingGrid.mono", V("f"), V("e")))))))));

    private static Formula Formula13() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                Eq(
                    Call("KingGrid.L", V("n"), V("k")),
                    SumOver(
                        "e",
                        Call("KingGrid.Edge", V("n"), V("k")),
                        Call(
                            "Nat.card",
                            Subtype(
                                "f",
                                Arrow(Call("KingGrid.Cell", V("n"), V("k")), Call("Fin", Num("4"))),
                                Call("KingGrid.DefectAt", V("e"), V("f"))))))));

    private static Formula Formula14() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                All(
                    "F",
                    Arrow(Call("KingGrid.Edge", V("n"), V("k")), Q("Nat")),
                    Eq(
                        SumOver("e", Call("KingGrid.Edge", V("n"), V("k")), App(V("F"), V("e"))),
                        Add(
                            Add(
                                Add(
                                    SumOver(
                                        "i",
                                        Call("Fin", V("n")),
                                        SumOver(
                                            "j",
                                            Call("Fin", Sub(V("k"), Num("1"))),
                                            App(V("F"), Call("KingGrid.Edge.H", V("i"), V("j"))))),
                                    SumOver(
                                        "i",
                                        Call("Fin", Sub(V("n"), Num("1"))),
                                        SumOver(
                                            "j",
                                            Call("Fin", V("k")),
                                            App(V("F"), Call("KingGrid.Edge.V", V("i"), V("j")))))),
                                SumOver(
                                    "i",
                                    Call("Fin", Sub(V("n"), Num("1"))),
                                    SumOver(
                                        "j",
                                        Call("Fin", Sub(V("k"), Num("1"))),
                                        App(V("F"), Call("KingGrid.Edge.D", V("i"), V("j")))))),
                            SumOver(
                                "i",
                                Call("Fin", Sub(V("n"), Num("1"))),
                                SumOver(
                                    "j",
                                    Call("Fin", Sub(V("k"), Num("1"))),
                                    App(V("F"), Call("KingGrid.Edge.A", V("i"), V("j"))))))))));

    private static Formula Formula15() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                And(
                    Typed(
                        Q("KingGrid.transposeEdge"),
                        Equivalence(
                            Call("KingGrid.Edge", V("n"), V("k")),
                            Call("KingGrid.Edge", V("k"), V("n")))),
                    And(
                        All(
                            "i",
                            Call("Fin", V("n")),
                            All(
                                "j",
                                Call("Fin", Sub(V("k"), Num("1"))),
                                Eq(
                                    Call("KingGrid.transposeEdge", Call("KingGrid.Edge.H", V("i"), V("j"))),
                                    Call("KingGrid.Edge.V", V("j"), V("i"))))),
                        And(
                            All(
                                "i",
                                Call("Fin", Sub(V("n"), Num("1"))),
                                All(
                                    "j",
                                    Call("Fin", V("k")),
                                    Eq(
                                        Call(
                                            "KingGrid.transposeEdge",
                                            Call("KingGrid.Edge.V", V("i"), V("j"))),
                                        Call("KingGrid.Edge.H", V("j"), V("i"))))),
                            And(
                                All(
                                    "i",
                                    Call("Fin", Sub(V("n"), Num("1"))),
                                    All(
                                        "j",
                                        Call("Fin", Sub(V("k"), Num("1"))),
                                        Eq(
                                            Call(
                                                "KingGrid.transposeEdge",
                                                Call("KingGrid.Edge.D", V("i"), V("j"))),
                                            Call("KingGrid.Edge.D", V("j"), V("i"))))),
                                All(
                                    "i",
                                    Call("Fin", Sub(V("n"), Num("1"))),
                                    All(
                                        "j",
                                        Call("Fin", Sub(V("k"), Num("1"))),
                                        Eq(
                                            Call(
                                                "KingGrid.transposeEdge",
                                                Call("KingGrid.Edge.A", V("i"), V("j"))),
                                            Call("KingGrid.Edge.A", V("j"), V("i")))))))))));

    private static Formula Formula16() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                And(
                    Typed(
                        Q("KingGrid.reflectEdge"),
                        Equivalence(
                            Call("KingGrid.Edge", V("n"), V("k")),
                            Call("KingGrid.Edge", V("n"), V("k")))),
                    And(
                        All(
                            "i",
                            Call("Fin", V("n")),
                            All(
                                "j",
                                Call("Fin", Sub(V("k"), Num("1"))),
                                Eq(
                                    Call("KingGrid.reflectEdge", Call("KingGrid.Edge.H", V("i"), V("j"))),
                                    Call("KingGrid.Edge.H", V("i"), Call("Fin.rev", V("j")))))),
                        And(
                            All(
                                "i",
                                Call("Fin", Sub(V("n"), Num("1"))),
                                All(
                                    "j",
                                    Call("Fin", V("k")),
                                    Eq(
                                        Call(
                                            "KingGrid.reflectEdge",
                                            Call("KingGrid.Edge.V", V("i"), V("j"))),
                                        Call("KingGrid.Edge.V", V("i"), Call("Fin.rev", V("j")))))),
                            And(
                                All(
                                    "i",
                                    Call("Fin", Sub(V("n"), Num("1"))),
                                    All(
                                        "j",
                                        Call("Fin", Sub(V("k"), Num("1"))),
                                        Eq(
                                            Call(
                                                "KingGrid.reflectEdge",
                                                Call("KingGrid.Edge.D", V("i"), V("j"))),
                                            Call("KingGrid.Edge.A", V("i"), Call("Fin.rev", V("j")))))),
                                All(
                                    "i",
                                    Call("Fin", Sub(V("n"), Num("1"))),
                                    All(
                                        "j",
                                        Call("Fin", Sub(V("k"), Num("1"))),
                                        Eq(
                                            Call(
                                                "KingGrid.reflectEdge",
                                                Call("KingGrid.Edge.A", V("i"), V("j"))),
                                            Call("KingGrid.Edge.D", V("i"), Call("Fin.rev", V("j"))))))))))));

    private static Formula Formula17() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                All(
                    "C",
                    Q("Type"),
                    All(
                        "f",
                        Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                        All(
                            "p",
                            Call("KingGrid.Cell", V("k"), V("n")),
                            Eq(
                                App(Call("KingGrid.transpose", V("f")), V("p")),
                                App(V("f"), Pair(Call("Prod.snd", V("p")), Call("Prod.fst", V("p"))))))))));

    private static Formula Formula18() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                All(
                    "C",
                    Q("Type"),
                    All(
                        "f",
                        Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                        All(
                            "e",
                            Call("KingGrid.Edge", V("n"), V("k")),
                            Iff(
                                Call(
                                    "KingGrid.mono",
                                    Call("KingGrid.transpose", V("f")),
                                    Call("KingGrid.transposeEdge", V("e"))),
                                Call("KingGrid.mono", V("f"), V("e"))))))));

    private static Formula Formula19() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                All(
                    "C",
                    Q("Type"),
                    All(
                        "e",
                        Call("KingGrid.Edge", V("n"), V("k")),
                        And(
                            Typed(
                                Call("KingGrid.transposeDefectEquiv", V("e")),
                                Equivalence(
                                    Subtype(
                                        "f",
                                        Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                                        Call("KingGrid.DefectAt", V("e"), V("f"))),
                                    Subtype(
                                        "f",
                                        Arrow(Call("KingGrid.Cell", V("k"), V("n")), V("C")),
                                        Call(
                                            "KingGrid.DefectAt",
                                            Call("KingGrid.transposeEdge", V("e")),
                                            V("f"))))),
                            All(
                                "f",
                                Subtype(
                                    "f",
                                    Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                                    Call("KingGrid.DefectAt", V("e"), V("f"))),
                                Eq(
                                    Value(App(Call("KingGrid.transposeDefectEquiv", V("e")), V("f"))),
                                    Call("KingGrid.transpose", Value(V("f"))))))))));

    private static Formula Formula20() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                All(
                    "C",
                    Q("Type"),
                    All(
                        "e",
                        Call("KingGrid.Edge", V("n"), V("k")),
                        And(
                            Typed(
                                Call("KingGrid.reflectDefectEquiv", V("e")),
                                Equivalence(
                                    Subtype(
                                        "f",
                                        Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                                        Call("KingGrid.DefectAt", V("e"), V("f"))),
                                    Subtype(
                                        "f",
                                        Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                                        Call(
                                            "KingGrid.DefectAt",
                                            Call("KingGrid.reflectEdge", V("e")),
                                            V("f"))))),
                            All(
                                "f",
                                Subtype(
                                    "f",
                                    Arrow(Call("KingGrid.Cell", V("n"), V("k")), V("C")),
                                    Call("KingGrid.DefectAt", V("e"), V("f"))),
                                Eq(
                                    Value(App(Call("KingGrid.reflectDefectEquiv", V("e")), V("f"))),
                                    Fn(
                                        "p",
                                        Call("KingGrid.Cell", V("n"), V("k")),
                                        App(
                                            Value(V("f")),
                                            Pair(
                                                Call("Prod.fst", V("p")),
                                                Call("Fin.rev", Call("Prod.snd", V("p")))))))))))));

    private static Formula Formula21() =>
        All(
            "n",
            Q("Nat"),
            All(
                "k",
                Q("Nat"),
                Imp(
                    Leq(Num("2"), V("n")),
                    Imp(
                        Leq(Num("2"), V("k")),
                        Eq(
                            Call("KingGrid.L", V("n"), V("k")),
                            Mul(Num("24"), Call("KingGrid.T", V("n"), V("k"))))))));

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
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Value(Formula a) => Call("Subtype.val", a);
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, b);
    private static Formula Subtype(string x, Formula t, Formula b) =>
        Seq(OpenBrace, V(x), Colon, Sp, t, Sp, Slash, Slash, Sp, Parenthesized(b), CloseBrace);
    private static Formula Fn(string x, Formula t, Formula b) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(x), t), Sp, Mapsto, Sp, b));
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Unique(string x, Formula t, Formula b) =>
        Seq(Exists, Bang, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string x, Formula t, Formula b) =>
        Seq(Sum, Underscore, Grp(Seq(V(x), Colon, Sp, t)), Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));

}
