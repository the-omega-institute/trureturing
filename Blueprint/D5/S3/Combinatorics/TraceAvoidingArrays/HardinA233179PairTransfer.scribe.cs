using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233179PairTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179PairTransfer.";
    private const string LeanPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proper pair-label patterns on a six-row ladder.", H("Six-row column transfer"),
        Blocks(
            Paragraph(Text("A column has six labels in Fin 3. Relabelling the palette gives "
                + "122 orbits of the 729 columns. Fifty orbits have compatible successors. "
                + "The remaining orbits have no successors and are combined into one zero "
                + "state, giving a transfer matrix with 51 states. Compatibility only compares "
                + "rows at distance at most one across consecutive columns.")),
            Node("Proper", "Proper pair-label patterns", ProperFormula(), false),
            Node("L", "The literal pair-label count", CountFormula(), false),
            Node("column", "Column coordinates", ColumnFormula(), false),
            Node("orbit", "Equality-pattern index", OrbitFormula(), false),
            Node("representatives", "The 122 equality-pattern representatives", RepresentativesFormula(), false),
            Node("class_rep", "Every column has its indexed representative", ClassRepFormula(), true),
            Node("initial_values", "Initial pair-label counts", InitialFormula(), true),
            Node("recurrence", "The shifted relation for L plus six", RecurrenceFormula(), true),
            Paragraph(Text("Finite column enumeration supplies every transition and initial "
                + "weight. TransferMatrix.cardMatrix gives the count at arbitrary width. "
                + "Twenty-six continuation vectors verify an order-24 vector relation after "
                + "one transition. TransferMatrix.scalarRelationShift propagates that relation. "
                + "Its coefficients sum to one, so adding the constant six preserves it. "
                + "The scalar relation starts at width 27; width 26 is supplied separately "
                + "by the initial values.")))));

    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233179");

    private static DocumentBlock Node(string name, string title, Formula formula, bool theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula ProperFormula()
    {
        var n = V("n"); var p = V("P"); var j = V("j"); var r = V("r"); var s = V("s");
        var next = Call("Fin.mk", Add(Val(j), D(1)), V("h"));
        var body = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(6)), All("s", Fin(D(6)), Imp(
                And(Le(Val(r), Add(Val(s), D(1))), Le(Val(s), Add(Val(r), D(1)))),
                Ne(App(p, Pair(r, j)), App(p, Pair(s, next))))))));
        return All("n", Q("Nat"), All("P", Arrow(Cells(n), Fin(D(3))),
            Eq(Own("Proper", p), Parenthesized(body))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var p = V("P"); var arrays = Arrow(Cells(n), Fin(D(3)));
        return All("n", Q("Nat"), Eq(Own("L", n), Call("Finset.card",
            Call("Finset.filter", Fn("P", arrays, Own("Proper", p)),
                Typed(Q("Finset.univ"), Call("Finset", arrays))))));
    }

    private static Formula PaletteTuple(int k) => k == 1 ? Fin(D(3)) : Product(Fin(D(3)), PaletteTuple(k-1));
    private static Formula Ite(Formula p, Formula a, Formula b) =>
        Seq(Q("if"), Sp, p, Sp, Q("then"), Sp, a, Sp, Q("else"), Sp, b);
    private static Formula Vector(params Formula[] xs) => Seq(Bang, OpenBracket,
        Seq(xs.SelectMany((x,i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x }).ToArray()), CloseBracket);
    private static Formula ColumnFormula() => All("c", PaletteTuple(6), Eq(Own("column", V("c")),
        Vector(Call("Prod.fst", V("c")), Call("Prod.fst", Call("Prod.snd", V("c"))),
            Call("Prod.fst", Call("Prod.snd", Call("Prod.snd", V("c")))),
            Call("Prod.fst", Call("Prod.snd", Call("Prod.snd", Call("Prod.snd", V("c"))))),
            Call("Prod.fst", Call("Prod.snd", Call("Prod.snd", Call("Prod.snd", Call("Prod.snd", V("c")))))),
            Call("Prod.snd", Call("Prod.snd", Call("Prod.snd", Call("Prod.snd", Call("Prod.snd", V("c")))))))));
    private static Formula ClassRepFormula()
    {
        var c = V("c"); var e = V("e");
        Formula Coordinate(int i)
        {
            Formula x = c;
            for (int j = 0; j < i; ++j) x = Call("Prod.snd", x);
            return i < 5 ? Call("Prod.fst", x) : x;
        }
        Formula Relabelled(int i) => i == 5 ? App(e, Coordinate(i)) :
            Pair(App(e, Coordinate(i)), Relabelled(i + 1));
        return All("c", PaletteTuple(6), new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("e"), Call("Equiv.Perm", Fin(D(3))),
            Eq(Relabelled(0), Own("representatives", Own("orbit", c)))));
    }
    private static Formula OrbitFormula() => All("c", PaletteTuple(6), Eq(Own("orbit", V("c")), Ite(Eq(Own("column", V("c"), Num(1)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(2)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(3)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(0), Num(1)), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(2), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(4))), Num(3), Num(4)))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(5), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(3))), Num(6), Num(7))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(3))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(8), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(3))), Num(9), Num(10))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(11), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(3))), Num(12), Num(13)))))), Ite(Eq(Own("column", V("c"), Num(3)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(14), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(2))), Num(15), Num(16))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(2))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(17), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(2))), Num(18), Num(19))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(20), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(2))), Num(21), Num(22))))), Ite(Eq(Own("column", V("c"), Num(3)), Own("column", V("c"), Num(2))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(23), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(2))), Num(24), Num(25))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(2))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(26), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(2))), Num(27), Num(28))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(29), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(2))), Num(30), Num(31))))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(32), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(2))), Num(33), Num(34))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(2))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(35), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(2))), Num(36), Num(37))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(38), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(2))), Num(39), Num(40)))))))), Ite(Eq(Own("column", V("c"), Num(2)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(3)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(41), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(42), Num(43))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(44), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(45), Num(46))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(47), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(48), Num(49))))), Ite(Eq(Own("column", V("c"), Num(3)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(50), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(51), Num(52))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(53), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(54), Num(55))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(56), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(57), Num(58))))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(59), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(60), Num(61))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(62), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(63), Num(64))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(65), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(66), Num(67))))))), Ite(Eq(Own("column", V("c"), Num(2)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(3)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(68), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(69), Num(70))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(71), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(72), Num(73))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(74), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(75), Num(76))))), Ite(Eq(Own("column", V("c"), Num(3)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(77), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(78), Num(79))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(80), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(81), Num(82))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(83), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(84), Num(85))))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(86), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(87), Num(88))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(89), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(90), Num(91))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(92), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(93), Num(94))))))), Ite(Eq(Own("column", V("c"), Num(3)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(95), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(96), Num(97))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(98), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(99), Num(100))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(101), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(102), Num(103))))), Ite(Eq(Own("column", V("c"), Num(3)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(104), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(105), Num(106))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(107), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(108), Num(109))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(110), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(111), Num(112))))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(0))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(113), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(114), Num(115))), Ite(Eq(Own("column", V("c"), Num(4)), Own("column", V("c"), Num(1))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(116), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(117), Num(118))), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(0))), Num(119), Ite(Eq(Own("column", V("c"), Num(5)), Own("column", V("c"), Num(1))), Num(120), Num(121))))))))))));
    private static Formula RepresentativesFormula() => Eq(Own("representatives"), Vector(
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(0), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(1), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(0), Pair(Num(2), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(0), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(1), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(1), Pair(Num(2), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(0), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(1), Pair(Num(2), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Pair(Num(0), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Pair(Num(0), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Pair(Num(0), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Pair(Num(1), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Pair(Num(1), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Pair(Num(1), Num(2)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Pair(Num(2), Num(0)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Pair(Num(2), Num(1)))))),
        Pair(Num(0), Pair(Num(1), Pair(Num(2), Pair(Num(2), Pair(Num(2), Num(2))))))));
    private static Formula InitialFormula()
    {
        var k = V("k");
        var values = Seq(Bang, OpenBracket,
            N("1458"), Comma, Sp,
            N("23346"), Comma, Sp,
            N("235824"), Comma, Sp,
            N("2986152"), Comma, Sp,
            N("33994188"), Comma, Sp,
            N("409408542"), Comma, Sp,
            N("4791504648"), Comma, Sp,
            N("56948232390"), Comma, Sp,
            N("671408641884"), Comma, Sp,
            N("7950212281224"), Comma, Sp,
            N("93923210426688"), Comma, Sp,
            N("1110971521842576"), Comma, Sp,
            N("13132515793768920"), Comma, Sp,
            N("155290791915166218"), Comma, Sp,
            N("1835954950424998884"), Comma, Sp,
            N("21708106678579996182"), Comma, Sp,
            N("256660237490505696204"), Comma, Sp,
            N("3034643594159596884672"), Comma, Sp,
            N("35879810376487028900160"), Comma, Sp,
            N("424224888649277811420648"), Comma, Sp,
            N("5015800426651629427544760"), Comma, Sp,
            N("59304188625218088516497046"), Comma, Sp,
            N("701180686835907546543927912"), Comma, Sp,
            N("8290387169164139913131170926"), Comma, Sp,
            N("98021089474277074253102673060"), Comma, Sp,
            N("1158948987790395127011466558572"), CloseBracket);
        return All("k", Fin(D(2,6)), Eq(Typed(Own("L", Add(Val(k), D(2))), Q("Int")),
            App(Typed(values, Arrow(Fin(D(2,6)), Q("Int"))), k)));
    }

    private static Formula RecurrenceFormula()
    {
        var n = V("n");
        Formula B(int i) => Add(Typed(Own("L", Add(n, Num(i))), Q("Int")), D(6));
        Formula rhs = Mul(N("7"), B(26));
        rhs = Add(rhs, Mul(N("103"), B(25)));
        rhs = Sub(rhs, Mul(N("365"), B(24)));
        rhs = Sub(rhs, Mul(N("2896"), B(23)));
        rhs = Add(rhs, Mul(N("7168"), B(22)));
        rhs = Add(rhs, Mul(N("32291"), B(21)));
        rhs = Sub(rhs, Mul(N("75471"), B(20)));
        rhs = Sub(rhs, Mul(N("161805"), B(19)));
        rhs = Add(rhs, Mul(N("426135"), B(18)));
        rhs = Add(rhs, Mul(N("333692"), B(17)));
        rhs = Sub(rhs, Mul(N("1225001"), B(16)));
        rhs = Sub(rhs, Mul(N("155206"), B(15)));
        rhs = Add(rhs, Mul(N("1850161"), B(14)));
        rhs = Sub(rhs, Mul(N("363389"), B(13)));
        rhs = Sub(rhs, Mul(N("1524689"), B(12)));
        rhs = Add(rhs, Mul(N("557502"), B(11)));
        rhs = Add(rhs, Mul(N("690388"), B(10)));
        rhs = Sub(rhs, Mul(N("312941"), B(9)));
        rhs = Sub(rhs, Mul(N("166928"), B(8)));
        rhs = Add(rhs, Mul(N("81406"), B(7)));
        rhs = Add(rhs, Mul(N("19997"), B(6)));
        rhs = Sub(rhs, Mul(N("9672"), B(5)));
        rhs = Sub(rhs, Mul(N("906"), B(4)));
        rhs = Add(rhs, Mul(N("420"), B(3)));
        return All("n", Q("Nat"), Eq(B(27), rhs));
    }

    private static Formula N(string digits) => D(digits.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = V(words[^1]);
        for (var i = words.Length - 2; i >= 0; --i)
            result = Seq(V(words[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Cells(Formula n) => Product(Fin(D(6)), Fin(n));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Own(string name, params Formula[] args) =>
        Call(LeanPrefix + name, args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) =>
        Parenthesized(Seq(x, Colon, Sp, type));

    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);





    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));


    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
}
