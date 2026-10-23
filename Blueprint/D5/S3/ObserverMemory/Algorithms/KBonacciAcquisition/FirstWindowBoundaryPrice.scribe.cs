using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FirstWindowBoundaryPriceDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryPrice.";
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var m = F.Id("m");
        var k = Subtract(Multiply(D(2), m), D(2));
        var scalar = Call("ZMod", D(2));
        var phase = Call("ZMod", Add(k, D(1)));
        var pair = Seq(scalar, Sp, Times, Sp, scalar);
        var y = F.Id("Y");
        var alphabet = F.Id("alphabet");
        var support = F.Id("support"); var A = F.Id("A"); var B = F.Id("B"); var f = F.Id("f");
        var v = F.Id("v"); var j = F.Id("j"); var s = F.Id("s");
        var initial = Call("some", Seq(Langle, Sp, v, Comma, new Formula.Negate(j), Comma, s, Rangle));
        var inside = All("v", scalar, All("h", nat,
            Imp(Call("Member", F.Id("h"), Apply( support, v)),
                And(Le(D(1), F.Id("h")), Le(F.Id("h"), m)))));
        var distinct = All("v", scalar,
            new Formula.Not(Eq(Apply( A, v), Apply( B, v))));
        var target = All("v", scalar, All("j", phase, All("s", nat,
            Imp(new Formula.Relation(s, FormulaRelationOperator.LessThan, k),
                Eq(Apply( f, initial),
                    Call("ifThenElse", Call("Member", Call("val", j), Apply( support, v)),
                        Apply( B, v), Apply( A, v)))))));
        var feasible = Call("OriginalPresetFeasible", k, m, alphabet, f, D(2));
        var image = Call("internalImage", m, support);
        var pi = Call("piFour", m, support);
        var result = And(
            Iff(feasible, pi),
            Imp(Eq(Call("card", image), D(1)), pi),
            Imp(Le(D(3), Call("card", image)), new Formula.Not(pi)));
        var statement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", F.Id("Bool"),
            All("support", Arrow(scalar, Call("Finset", nat)),
            All("A", Arrow(scalar, y), All("B", Arrow(scalar, y),
            All("f", Arrow(Call("Option", Call("LiveRecord", k)), y),
            Imp(And(Le(D(5), m), inside, distinct, target,
                Eq(Call("card", Call("fullImage", m, support)), D(4))), result))))))));
        var cost = Call("presetCost", m, support);
        var n = Call("card", Call("fullImage", m, support));
        var union = Call("Union", Apply(support, D(0)), Apply(support, D(1)));
        var budget = F.Id("d"); var z = F.Id("z");
        var unique = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("z"), pair,
            And(new Formula.Not(Eq(z, D(0))),
                Eq(Call("fullImage", m, support), Call("Insert", D(0), Call("Singleton", z))),
                All("j", phase, Eq(Call("membership", m, support, j),
                    Call("ifThenElse", Call("Member", Call("val", j), union), z, D(0)))),
                All("v", scalar, new Formula.Logic(Eq(Apply(support, v), Call("Empty")),
                    FormulaLogicOperator.Or, Eq(Apply(support, v), union))),
                new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("v"), scalar,
                    Eq(Apply(support, v), union))));
        var q = Call("OriginalRecord", k, Call("flattenAllowedHistory", F.Id("history")));
        var free = Call("output", k, Call("flattenAllowedHistory", F.Id("history")));
        var stream = F.Id("stream"); var stop = F.Id("stop"); var issued = F.Id("issued");
        var selector = Call("presetSelector", stream, stop);
        var trace = Call("PaidTrace", selector, free, q, Call("EmptyList"), issued, Apply(f, q));
        var historyType = Call("List", Call("AllowedBlock", k, m, alphabet));
        var actualTraces = All("history", historyType,
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("issued"), Call("Archive", m),
                And(trace, Le(Call("length", issued), cost),
                    Eq(Call("length", Call("archiveWords", issued)), Multiply(m, Call("length", issued))))));
        var worst = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("history"), historyType,
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("issued"), Call("Archive", m),
                And(trace, Eq(Call("length", issued), cost),
                    Eq(Call("length", Call("archiveWords", issued)), Multiply(m, cost)))));
        var paid = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("stream"),
            Arrow(nat, Arrow(Call("Fin", m), F.Id("Bool"))),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("stop"),
                Arrow(Call("Option", scalar), Arrow(Call("Archive", m), Call("Option", y))),
                And(Call("SelectorLegal", k, alphabet, selector),
                    Eq(Apply(stop, Call("none"), Call("EmptyList")), Call("some", Apply(f, Call("none")))), actualTraces, worst)));
        var parityTable = Imp(Eq(n, D(4)), And(
            Imp(Eq(Call("card", image), D(1)), pi),
            Imp(Le(D(3), Call("card", image)), new Formula.Not(pi)),
            All("z", pair, Imp(And(new Formula.Not(Eq(z, D(0))),
                Eq(image, Call("Insert", D(0), Call("Singleton", z)))),
                Iff(pi, Call("Odd", Call("card", Call("internalFiber", m, support, z)))))),
            Imp(And(Eq(Call("card", image), D(2)), new Formula.Not(Call("Member", D(0), image))),
                Iff(pi, Call("Even", Call("boundaryParity", m, support))))));
        var mainResult = And(Eq(Call("GlobalPresetPrice", k, m, alphabet, f), Call("natCast", cost)),
            All("d", nat, Iff(Call("OriginalPresetFeasible", k, m, alphabet, f, budget), Le(cost, budget))),
            Iff(Eq(n, D(1)), And(Eq(Apply(support, D(0)), Call("Empty")),
                Eq(Apply(support, D(1)), Call("Empty")))), Imp(Eq(n, D(2)), unique), parityTable,
            All("b", nat, Iff(Call("PresetBitFeasible", m, alphabet, f, F.Id("b")), Le(Multiply(m, cost), F.Id("b")))), paid);
        var mainStatement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", F.Id("Bool"),
            All("support", Arrow(scalar, Call("Finset", nat)), All("A", Arrow(scalar, y),
            All("B", Arrow(scalar, y), All("f", Arrow(Call("Option", Call("LiveRecord", k)), y),
            Imp(And(Le(D(5), m), inside, distinct, target), mainResult))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The extreme rows of the expanded four-label table are exact on the complete original source.",
            H("Four-label table extremes"),
            Blocks(Describe.Lean(
                DescribeId.Create("original-first-window-table-extremes"),
                DeclarationHandle.Create(Owner + "original_first_window_table_extremes"),
                H("One internal class and three-or-more internal classes"),
                StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix m>=5, k=2m-2 and the full original first-window family. The two supports "
                        + "are retained as ordered membership pairs, so cross-value label coincidences "
                        + "do not identify distinct membership classes. The theorem keeps arbitrary Y, "
                        + "both original alphabets, all actual INITIAL phases and inherited tails, and "
                        + "the original complete-block feasibility contract.")),
                    Paragraph(Text(
                        "The existing four-label compatibility result supplies the exact original "
                        + "feasibility iff Pi4. The table isolates two extreme rows. If the "
                        + "internal image has one class, the erase of any pivot has cardinality at most "
                        + "one. The full image has four classes, so the internal class cannot be the "
                        + "base: otherwise the boundary phases and the exterior base could supply at most "
                        + "three classes. Hence the base clause of Pi4 is vacuous and Pi4 holds.")),
                    Paragraph(Text(
                        "If the internal image has at least three classes, erasing any one pivot leaves "
                        + "at least two classes. This directly contradicts the first Pi4 clause, whether "
                        + "or not the pivot lies in the internal image. The proof uses the actual phase "
                        + "image and its finite-set cardinality; it does not enumerate literal words or "
                        + "replace the physical source by an unrestricted parity query.")),
                    Paragraph(Text("The full-image decomposition is proved from the actual phase partition into "
                        + "exterior, boundary and internal phases. The saturated compatibility theorem is stated at "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryFourLabels"),
                        Text("."))),
                DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("original-first-window-preset-price"),
                    DeclarationHandle.Create(Owner + "original_first_window_preset_price"),
                    H("The exact price of one common literal stream"),
                    StatementSource.FromAuthor(Disp(mainStatement)), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("The full image counts each phase once. One class is equivalent to two empty supports. "
                            + "With two classes, every member of the union carries one nonzero membership pair; each component "
                            + "support is either empty or that union, and at least one equals the union. This includes equal "
                            + "supports and an empty value fibre. Cross-value coincidences of output labels do not merge membership pairs.")),
                        Paragraph(Text("The price is zero for one class, binaryCost of the support union for two classes, "
                            + "and two or three for three and four classes according to Pi3 or Pi4. In the four-class branch, "
                            + "one internal class always gives two, whereas three or more internal classes give three. "
                            + "The same literal stream serves both free values; stopping and decoding use each source's own archive.")),
                        Paragraph(Text("For the joined one-block obstruction, two phases with the same actual root charge "
                            + "produce the same component label at each remembered free value. Their ordered membership pairs "
                            + "therefore agree. The full image injects into the two possible charges. This uses jointly realized "
                            + "original histories at tail zero, without assuming that the two component decoders stop together.")),
                        Paragraph(Text("The upper bounds use the safe binary, boundary-compatible two-block, and pulse/donor "
                            + "three-block constructions. The lower bounds quantify every legal common stream and stopping rule, "
                            + "including early stops and rejecting blocks. OriginalPresetFeasible uses unknown actual histories, "
                            + "immutable INITIAL targets, both alphabets and arbitrary inherited tails. An initially rejected history "
                            + "has its independent bottom label and stops at zero. The theorem gives the minimum block budget; "
                            + "each issued block has exactly m bits by the chronological archive-length law.")),
                        Paragraph(Text("The binary and three-block physical constructions are supplied by "),
                            Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment"),
                            Text("; the two-block relations and safe selected inverses are supplied by "),
                            Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCompatibility"),
                            Text(" and "),
                            Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryFourLabels"), Text(".")),
                        Paragraph(Text("The component lower bounds use the actual adaptive law at "),
                            Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAdaptive"),
                            Text(". All four expanded rows use phase-once multiplicities. For K={0,z}, the two boundary-only labels each occur once; the pivot is zero precisely when the internal z class is odd. When K has two classes and excludes zero, the complement has two labels, zero and z. Their multiplicity parities are equal precisely when the pivot lies in K. The exterior phase partition has m-1 phases plus each boundary outside K, giving boundaryParity. A minimizing common selector also has a jointly realized original history whose actual trace attains the minimum; every trace counts only emitted blocks. The exact bit budget is m times that minimum."))),
                    DescribeRole.Theorem))));
    }
}
