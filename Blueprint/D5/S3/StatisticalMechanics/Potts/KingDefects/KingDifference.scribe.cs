using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class KingDifferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/KingDifference.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: KingDifference"),
        Blocks(
            Node("K", "The additive Klein four group", Formula0(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Addition is componentwise modulo two; every element is its own additive inverse."),
            Node("NZPair", "Ordered distinct nonzero colours",
                Eq(Q("KingDifference.NZPair"),
                    Subtype("pq", Product(Q("KingDifference.K"), Q("KingDifference.K")),
                        And(Ne(Call("Prod.fst", V("pq")), Num("0")),
                            And(Ne(Call("Prod.snd", V("pq")), Num("0")),
                                Ne(Call("Prod.fst", V("pq")), Call("Prod.snd", V("pq"))))))),
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                "Choose two different nonzero colours, retaining their order."),
            Node("nz_pair_card", "Six ordered colour pairs",
                Eq(Call("Nat.card", Q("KingDifference.NZPair")), Num("6")),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                "The three nonzero colours give three choices for the first entry and two for the second."),
            Node("add_eq_zero", "Zero sums identify equal colours",
                All("a", Q("KingDifference.K"), All("b", Q("KingDifference.K"),
                    Iff(Eq(Add(V("a"), V("b")), Num("0")), Eq(V("a"), V("b"))))),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Since each colour is its own additive inverse, two colours have zero sum exactly when they agree."),
            Node("DiffField", "Horizontal and vertical differences", Formula1(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The record has fields h and v of the displayed types. They assign differences to horizontal and vertical bonds, respectively."),
            Node("Cocycle", "Compatibility around every square", Formula2(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The two sums along the two-step paths across each elementary square agree."),
            Node("differentiate", "Take adjacent colour differences", Formula3(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Over this group, a difference is the sum of the endpoint colours."),
            Node("integrate", "Integrate from a root colour", Formula4(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Starting with root colour t, the path goes down column zero and then across the target row. Fin.partialSum adds entries strictly before the indicated endpoint."),
            Node("differentiate_integrate", "Recover a compatible difference field", Formula5(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Compatibility around squares makes the path integral recover every horizontal and vertical difference. The consumed private helper psum_add obtains partial-sum additivity directly from List.sum_map_add after unfolding Fin.partialSum."),
            Node("edgeValue", "Differences on all four orientations", Formula6(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Diagonal differences are sums of two adjacent differences along a two-step path."),
            Node("RawAdmissible", "A compatible field with a single zero bond", Formula7(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The field is compatible and precisely the selected bond has zero difference."),
            Node("raw_differentiate_iff", "Zero differences are monochromatic bonds", Formula8(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Differentiation translates exactly one monochromatic bond into exactly one zero difference."),
            Node("defectIntegrationEquiv", "Separate root colour from differences", Formula9(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "A colouring is determined by its root colour and admissible difference field. The inverse integrates the field from that root."),
            Node("N_e", "Count admissible fields for a fixed bond", Formula10(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "This is also the number of colourings with the prescribed defect and root colour zero."),
            Node("count_fixed_edge", "Four choices of root colour", Formula11(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "After identifying the four colours with the Klein four group, the root colour has four independent choices."),
            Node("BlockAvoids", "A square avoids the defective bond", Formula12(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "None of the square's four side bonds or two diagonal bonds is the selected defect."),
            Node("goodBlock_of_raw", "Opposite differences agree away from the defect", Formula13(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "A defect-free square is rainbow. Its opposite differences agree, and its horizontal and vertical differences are nonzero and distinct."),
            Node("horizontal_slot_eq", "Constant horizontal slots", Formula14(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Agreement of opposite differences propagates through every intervening square that avoids the selected defect."),
            Node("vertical_slot_eq", "Constant vertical slots", Formula15(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Agreement of opposite differences propagates through every intervening square that avoids the selected defect."),
            Node("N_H", "Sum over horizontal defect positions", Formula16(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The summands count admissible fields for each defect position of this orientation."),
            Node("N_D", "Sum over descending diagonal defect positions", Formula17(),
                DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "The summands count admissible fields for each defect position of this orientation."),
            Node("count_by_kind", "Count by orientation and remove colour labels", Formula18(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "Transposition identifies vertical with horizontal positions and reflection identifies the two diagonal orientations. Four root colours and twenty-four colour permutations leave a factor of six."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Formula0() =>
        Eq(Q("KingDifference.K"), Product(Call("ZMod", Num("2")), Call("ZMod", Num("2"))));

    private static Formula Formula1() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                And(
                    Typed(
                        Q("KingDifference.DiffField.mk"),
                        Arrow(
                            Arrow(
                                Call("Fin", Add(V("N"), Num("1"))),
                                Arrow(Call("Fin", V("M")), Q("KingDifference.K"))),
                            Arrow(
                                Arrow(
                                    Call("Fin", V("N")),
                                    Arrow(Call("Fin", Add(V("M"), Num("1"))), Q("KingDifference.K"))),
                                Call("KingDifference.DiffField", V("N"), V("M"))))),
                    And(
                        Typed(
                            Q("KingDifference.DiffField.h"),
                            Arrow(
                                Call("KingDifference.DiffField", V("N"), V("M")),
                                Arrow(
                                    Call("Fin", Add(V("N"), Num("1"))),
                                    Arrow(Call("Fin", V("M")), Q("KingDifference.K"))))),
                        Typed(
                            Q("KingDifference.DiffField.v"),
                            Arrow(
                                Call("KingDifference.DiffField", V("N"), V("M")),
                                Arrow(
                                    Call("Fin", V("N")),
                                    Arrow(Call("Fin", Add(V("M"), Num("1"))), Q("KingDifference.K")))))))));

    private static Formula Formula2() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "s",
                    Call("KingDifference.DiffField", V("N"), V("M")),
                    Iff(
                        Call("KingDifference.Cocycle", V("s")),
                        All(
                            "i",
                            Call("Fin", V("N")),
                            All(
                                "j",
                                Call("Fin", V("M")),
                                Eq(
                                    Add(
                                        Call(
                                            "KingDifference.DiffField.h",
                                            V("s"),
                                            Call("Fin.castSucc", V("i")),
                                            V("j")),
                                        Call(
                                            "KingDifference.DiffField.v",
                                            V("s"),
                                            V("i"),
                                            Call("Fin.succ", V("j")))),
                                    Add(
                                        Call(
                                            "KingDifference.DiffField.v",
                                            V("s"),
                                            V("i"),
                                            Call("Fin.castSucc", V("j"))),
                                        Call(
                                            "KingDifference.DiffField.h",
                                            V("s"),
                                            Call("Fin.succ", V("i")),
                                            V("j"))))))))));

    private static Formula Formula3() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "f",
                    Arrow(
                        Call("KingGrid.Cell", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                        Q("KingDifference.K")),
                    And(
                        All(
                            "i",
                            Call("Fin", Add(V("N"), Num("1"))),
                            All(
                                "j",
                                Call("Fin", V("M")),
                                Eq(
                                    Call(
                                        "KingDifference.DiffField.h",
                                        Call("KingDifference.differentiate", V("f")),
                                        V("i"),
                                        V("j")),
                                    Add(
                                        App(V("f"), Pair(V("i"), Call("Fin.castSucc", V("j")))),
                                        App(V("f"), Pair(V("i"), Call("Fin.succ", V("j")))))))),
                        All(
                            "i",
                            Call("Fin", V("N")),
                            All(
                                "j",
                                Call("Fin", Add(V("M"), Num("1"))),
                                Eq(
                                    Call(
                                        "KingDifference.DiffField.v",
                                        Call("KingDifference.differentiate", V("f")),
                                        V("i"),
                                        V("j")),
                                    Add(
                                        App(V("f"), Pair(Call("Fin.castSucc", V("i")), V("j"))),
                                        App(V("f"), Pair(Call("Fin.succ", V("i")), V("j")))))))))));

    private static Formula Formula4() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "t",
                    Q("KingDifference.K"),
                    All(
                        "s",
                        Call("KingDifference.DiffField", V("N"), V("M")),
                        All(
                            "p",
                            Call("KingGrid.Cell", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                            Eq(
                                App(Call("KingDifference.integrate", V("t"), V("s")), V("p")),
                                Add(
                                    Add(
                                        V("t"),
                                        Call(
                                            "Fin.partialSum",
                                            Fn(
                                                "i",
                                                Call("Fin", V("N")),
                                                Call("KingDifference.DiffField.v", V("s"), V("i"), Num("0"))),
                                            Call("Prod.fst", V("p")))),
                                    Call(
                                        "Fin.partialSum",
                                        App(
                                            Q("KingDifference.DiffField.h"),
                                            V("s"),
                                            Call("Prod.fst", V("p"))),
                                        Call("Prod.snd", V("p"))))))))));

    private static Formula Formula5() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "t",
                    Q("KingDifference.K"),
                    All(
                        "s",
                        Call("KingDifference.DiffField", V("N"), V("M")),
                        Imp(
                            Call("KingDifference.Cocycle", V("s")),
                            Eq(
                                Call(
                                    "KingDifference.differentiate",
                                    Call("KingDifference.integrate", V("t"), V("s"))),
                                V("s")))))));

    private static Formula Formula6() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "s",
                    Call("KingDifference.DiffField", V("N"), V("M")),
                    And(
                        All(
                            "i",
                            Call("Fin", Add(V("N"), Num("1"))),
                            All(
                                "j",
                                Call("Fin", V("M")),
                                Eq(
                                    Call(
                                        "KingDifference.edgeValue",
                                        V("s"),
                                        Call("KingGrid.Edge.H", V("i"), V("j"))),
                                    Call("KingDifference.DiffField.h", V("s"), V("i"), V("j"))))),
                        And(
                            All(
                                "i",
                                Call("Fin", V("N")),
                                All(
                                    "j",
                                    Call("Fin", Add(V("M"), Num("1"))),
                                    Eq(
                                        Call(
                                            "KingDifference.edgeValue",
                                            V("s"),
                                            Call("KingGrid.Edge.V", V("i"), V("j"))),
                                        Call("KingDifference.DiffField.v", V("s"), V("i"), V("j"))))),
                            And(
                                All(
                                    "i",
                                    Call("Fin", V("N")),
                                    All(
                                        "j",
                                        Call("Fin", V("M")),
                                        Eq(
                                            Call(
                                                "KingDifference.edgeValue",
                                                V("s"),
                                                Call("KingGrid.Edge.D", V("i"), V("j"))),
                                            Add(
                                                Call(
                                                    "KingDifference.DiffField.h",
                                                    V("s"),
                                                    Call("Fin.castSucc", V("i")),
                                                    V("j")),
                                                Call(
                                                    "KingDifference.DiffField.v",
                                                    V("s"),
                                                    V("i"),
                                                    Call("Fin.succ", V("j"))))))),
                                All(
                                    "i",
                                    Call("Fin", V("N")),
                                    All(
                                        "j",
                                        Call("Fin", V("M")),
                                        Eq(
                                            Call(
                                                "KingDifference.edgeValue",
                                                V("s"),
                                                Call("KingGrid.Edge.A", V("i"), V("j"))),
                                            Add(
                                                Call(
                                                    "KingDifference.DiffField.h",
                                                    V("s"),
                                                    Call("Fin.castSucc", V("i")),
                                                    V("j")),
                                                Call(
                                                    "KingDifference.DiffField.v",
                                                    V("s"),
                                                    V("i"),
                                                    Call("Fin.castSucc", V("j")))))))))))));

    private static Formula Formula7() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "e",
                    Call("KingGrid.Edge", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                    All(
                        "s",
                        Call("KingDifference.DiffField", V("N"), V("M")),
                        Iff(
                            Call("KingDifference.RawAdmissible", V("e"), V("s")),
                            And(
                                Call("KingDifference.Cocycle", V("s")),
                                All(
                                    "d",
                                    Call("KingGrid.Edge", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                                    Iff(
                                        Eq(Call("KingDifference.edgeValue", V("s"), V("d")), Num("0")),
                                        Eq(V("d"), V("e"))))))))));

    private static Formula Formula8() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "f",
                    Arrow(
                        Call("KingGrid.Cell", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                        Q("KingDifference.K")),
                    All(
                        "e",
                        Call("KingGrid.Edge", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                        Iff(
                            Call(
                                "KingDifference.RawAdmissible",
                                V("e"),
                                Call("KingDifference.differentiate", V("f"))),
                            Call("KingGrid.DefectAt", V("e"), V("f")))))));

    private static Formula Formula9() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "e",
                    Call("KingGrid.Edge", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                    And(
                        Typed(
                            Call("KingDifference.defectIntegrationEquiv", V("e")),
                            Equivalence(
                                Subtype(
                                    "f",
                                    Arrow(
                                        Call("KingGrid.Cell", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                                        Q("KingDifference.K")),
                                    Call("KingGrid.DefectAt", V("e"), V("f"))),
                                Product(
                                    Q("KingDifference.K"),
                                    Subtype(
                                        "s",
                                        Call("KingDifference.DiffField", V("N"), V("M")),
                                        Call("KingDifference.RawAdmissible", V("e"), V("s")))))),
                        All(
                            "f",
                            Subtype(
                                "f",
                                Arrow(
                                    Call("KingGrid.Cell", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                                    Q("KingDifference.K")),
                                Call("KingGrid.DefectAt", V("e"), V("f"))),
                            And(
                                Eq(
                                    Call(
                                        "Prod.fst",
                                        App(Call("KingDifference.defectIntegrationEquiv", V("e")), V("f"))),
                                    App(Value(V("f")), Pair(Num("0"), Num("0")))),
                                Eq(
                                    Value(
                                        Call(
                                            "Prod.snd",
                                            App(
                                                Call("KingDifference.defectIntegrationEquiv", V("e")),
                                                V("f")))),
                                    Call("KingDifference.differentiate", Value(V("f"))))))))));

    private static Formula Formula10() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "e",
                    Call("KingGrid.Edge", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                    Eq(
                        Call("KingDifference.N_e", V("e")),
                        Call(
                            "Nat.card",
                            Subtype(
                                "s",
                                Call("KingDifference.DiffField", V("N"), V("M")),
                                Call("KingDifference.RawAdmissible", V("e"), V("s"))))))));

    private static Formula Formula11() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "e",
                    Call("KingGrid.Edge", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                    Eq(
                        Call(
                            "Nat.card",
                            Subtype(
                                "f",
                                Arrow(
                                    Call("KingGrid.Cell", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                                    Call("Fin", Num("4"))),
                                Call("KingGrid.DefectAt", V("e"), V("f")))),
                        Mul(Num("4"), Call("KingDifference.N_e", V("e")))))));

    private static Formula Formula12() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "e",
                    Call("KingGrid.Edge", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                    All(
                        "i",
                        Call("Fin", V("N")),
                        All(
                            "j",
                            Call("Fin", V("M")),
                            Iff(
                                Call("KingDifference.BlockAvoids", V("e"), V("i"), V("j")),
                                And(
                                    Ne(
                                        Call("KingGrid.Edge.H", Call("Fin.castSucc", V("i")), V("j")),
                                        V("e")),
                                    And(
                                        Ne(
                                            Call("KingGrid.Edge.V", V("i"), Call("Fin.castSucc", V("j"))),
                                            V("e")),
                                        And(
                                            Ne(Call("KingGrid.Edge.D", V("i"), V("j")), V("e")),
                                            And(
                                                Ne(Call("KingGrid.Edge.A", V("i"), V("j")), V("e")),
                                                And(
                                                    Ne(
                                                        Call(
                                                            "KingGrid.Edge.V",
                                                            V("i"),
                                                            Call("Fin.succ", V("j"))),
                                                        V("e")),
                                                    Ne(
                                                        Call(
                                                            "KingGrid.Edge.H",
                                                            Call("Fin.succ", V("i")),
                                                            V("j")),
                                                        V("e")))))))))))));

    private static Formula Formula13() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "e",
                    Call("KingGrid.Edge", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                    All(
                        "s",
                        Call("KingDifference.DiffField", V("N"), V("M")),
                        Imp(
                            Call("KingDifference.RawAdmissible", V("e"), V("s")),
                            All(
                                "i",
                                Call("Fin", V("N")),
                                All(
                                    "j",
                                    Call("Fin", V("M")),
                                    Imp(
                                        Call("KingDifference.BlockAvoids", V("e"), V("i"), V("j")),
                                        And(
                                            Eq(
                                                Call(
                                                    "KingDifference.DiffField.h",
                                                    V("s"),
                                                    Call("Fin.castSucc", V("i")),
                                                    V("j")),
                                                Call(
                                                    "KingDifference.DiffField.h",
                                                    V("s"),
                                                    Call("Fin.succ", V("i")),
                                                    V("j"))),
                                            And(
                                                Eq(
                                                    Call(
                                                        "KingDifference.DiffField.v",
                                                        V("s"),
                                                        V("i"),
                                                        Call("Fin.castSucc", V("j"))),
                                                    Call(
                                                        "KingDifference.DiffField.v",
                                                        V("s"),
                                                        V("i"),
                                                        Call("Fin.succ", V("j")))),
                                                And(
                                                    Ne(
                                                        Call(
                                                            "KingDifference.DiffField.h",
                                                            V("s"),
                                                            Call("Fin.castSucc", V("i")),
                                                            V("j")),
                                                        Num("0")),
                                                    And(
                                                        Ne(
                                                            Call(
                                                                "KingDifference.DiffField.v",
                                                                V("s"),
                                                                V("i"),
                                                                Call("Fin.castSucc", V("j"))),
                                                            Num("0")),
                                                        Ne(
                                                            Call(
                                                                "KingDifference.DiffField.h",
                                                                V("s"),
                                                                Call("Fin.castSucc", V("i")),
                                                                V("j")),
                                                            Call(
                                                                "KingDifference.DiffField.v",
                                                                V("s"),
                                                                V("i"),
                                                                Call("Fin.castSucc", V("j"))))))))))))))));

    private static Formula Formula14() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "e",
                    Call("KingGrid.Edge", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                    All(
                        "s",
                        Call("KingDifference.DiffField", V("N"), V("M")),
                        Imp(
                            Call("KingDifference.RawAdmissible", V("e"), V("s")),
                            All(
                                "j",
                                Call("Fin", V("M")),
                                All(
                                    "a",
                                    Call("Fin", Add(V("N"), Num("1"))),
                                    All(
                                        "b",
                                        Call("Fin", Add(V("N"), Num("1"))),
                                        Imp(
                                            Leq(V("a"), V("b")),
                                            Imp(
                                                All(
                                                    "i",
                                                    Call("Fin", V("N")),
                                                    Imp(
                                                        Leq(Val(V("a")), Val(V("i"))),
                                                        Imp(
                                                            Lt(Val(V("i")), Val(V("b"))),
                                                            Call(
                                                                "KingDifference.BlockAvoids",
                                                                V("e"),
                                                                V("i"),
                                                                V("j"))))),
                                                Eq(
                                                    Call(
                                                        "KingDifference.DiffField.h",
                                                        V("s"),
                                                        V("a"),
                                                        V("j")),
                                                    Call(
                                                        "KingDifference.DiffField.h",
                                                        V("s"),
                                                        V("b"),
                                                        V("j")))))))))))));

    private static Formula Formula15() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                All(
                    "e",
                    Call("KingGrid.Edge", Add(V("N"), Num("1")), Add(V("M"), Num("1"))),
                    All(
                        "s",
                        Call("KingDifference.DiffField", V("N"), V("M")),
                        Imp(
                            Call("KingDifference.RawAdmissible", V("e"), V("s")),
                            All(
                                "i",
                                Call("Fin", V("N")),
                                All(
                                    "a",
                                    Call("Fin", Add(V("M"), Num("1"))),
                                    All(
                                        "b",
                                        Call("Fin", Add(V("M"), Num("1"))),
                                        Imp(
                                            Leq(V("a"), V("b")),
                                            Imp(
                                                All(
                                                    "j",
                                                    Call("Fin", V("M")),
                                                    Imp(
                                                        Leq(Val(V("a")), Val(V("j"))),
                                                        Imp(
                                                            Lt(Val(V("j")), Val(V("b"))),
                                                            Call(
                                                                "KingDifference.BlockAvoids",
                                                                V("e"),
                                                                V("i"),
                                                                V("j"))))),
                                                Eq(
                                                    Call(
                                                        "KingDifference.DiffField.v",
                                                        V("s"),
                                                        V("i"),
                                                        V("a")),
                                                    Call(
                                                        "KingDifference.DiffField.v",
                                                        V("s"),
                                                        V("i"),
                                                        V("b")))))))))))));

    private static Formula Formula16() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                Eq(
                    Call("KingDifference.N_H", V("N"), V("M")),
                    SumOver(
                        "i",
                        Call("Fin", Add(V("N"), Num("1"))),
                        SumOver(
                            "j",
                            Call("Fin", V("M")),
                            Call("KingDifference.N_e", Call("KingGrid.Edge.H", V("i"), V("j"))))))));

    private static Formula Formula17() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                Eq(
                    Call("KingDifference.N_D", V("N"), V("M")),
                    SumOver(
                        "i",
                        Call("Fin", V("N")),
                        SumOver(
                            "j",
                            Call("Fin", V("M")),
                            Call("KingDifference.N_e", Call("KingGrid.Edge.D", V("i"), V("j"))))))));

    private static Formula Formula18() =>
        All(
            "N",
            Q("Nat"),
            All(
                "M",
                Q("Nat"),
                Imp(
                    Leq(Num("1"), V("N")),
                    Imp(
                        Leq(Num("1"), V("M")),
                        Eq(
                            Add(
                                Add(
                                    Call("KingDifference.N_H", V("N"), V("M")),
                                    Call("KingDifference.N_H", V("M"), V("N"))),
                                Mul(Num("2"), Call("KingDifference.N_D", V("N"), V("M")))),
                            Mul(Num("6"), Call("KingGrid.T", Add(V("N"), Num("1")), Add(V("M"), Num("1")))))))));

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
    private static Formula Val(Formula a) => Call("Fin.val", a);
    private static Formula Value(Formula a) => Call("Subtype.val", a);
    private static Formula Subtype(string x, Formula t, Formula b) =>
        Seq(OpenBrace, V(x), Colon, Sp, t, Sp, Slash, Slash, Sp, Parenthesized(b), CloseBrace);
    private static Formula Fn(string x, Formula t, Formula b) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(x), t), Sp, Mapsto, Sp, b));
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string x, Formula t, Formula b) =>
        Seq(Sum, Underscore, Grp(Seq(V(x), Colon, Sp, t)), Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));

}
