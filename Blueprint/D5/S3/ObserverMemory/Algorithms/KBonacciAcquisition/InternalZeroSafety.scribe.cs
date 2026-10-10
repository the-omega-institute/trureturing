using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class InternalZeroSafetyDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/InternalZeroSafety.";
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((left, right) => new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula Arrow(Formula left, Formula right) => Seq(left, Sp, To, Sp, right);
    private static Formula Apply(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Open, LambdaLower, Sp, Open, F.Id(name), Colon, type, Close, Comma, Sp, body, Close);
    private static Formula Record(Formula v, Formula phase, Formula s) =>
        Call("some", Seq(Langle, Sp, v, Comma, phase, Comma, s, Rangle));
    private static Formula Index(Formula value, Formula bound) =>
        Seq(Langle, Sp, value, Rangle, Underscore, Grp(bound));

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var bit = F.Id("Bool"); var scalar = Call("ZMod", D(2));
        var k = F.Id("k"); var m = F.Id("m"); var w = F.Id("w");
        var i = F.Id("i"); var v = F.Id("v"); var phase = F.Id("phase");
        var s = F.Id("s"); var j = F.Id("j"); var alphabet = F.Id("alphabet");
        var group = Call("ZMod", Add(k, D(1)));
        var wordType = Arrow(Call("Fin", m), bit);
        var tail = Call("tailAfter", D(0), w);
        var incoming = Or(Lt(Add(s, Call("val", i)), k),
            Equal(Apply(w, Index(D(0), m)), F.Id("false")));
        var execution = All("k", nat, All("m", nat, All("w", wordType,
            All("i", Call("Fin", m), All("v", scalar, All("phase", group, All("s", nat,
                Imp(And(Le(D(2), k), Lt(m, k), Equal(Apply(w, i), F.Id("false")),
                    Lt(s, k), incoming), And(
                    Equal(Call("runBits", k, w, Record(v, phase, s)),
                        Record(Add(v, Call("wordIncrement", k, phase, w)),
                            Add(phase, m), tail)),
                    Le(tail, Subtract(Subtract(m, D(1)), Call("val", i))))))))))));

        var marked = F.Id("marked"); var e = F.Id("e"); var a = F.Id("a"); var b = F.Id("b");
        var rowType = Arrow(nat, scalar);
        var entryType = Seq(Open, rowType, Close, Sp, Times, Sp, Call("Fin", m));
        var rows = Call("mapFirst", marked);
        var actions = Call("chargeBlocks", k, m, alphabet, rows);
        var current = Record(v, new Formula.Negate(j), s);
        var start = Record(D(0), D(0), D(0));
        var archive = Call("fixedBlockArchive", actions, current);
        var predicted = Call("chargeArchive", k, m, rows, v, j);
        var row = Call("row", e); var mark = Call("mark", e);
        var sum = Seq(F.Sum, Underscore, Grp(Seq(F.Id("h"), InMacro, Sp,
            Call("range", Add(m, D(1))))), Sp, Apply(row, F.Id("h")));
        var rowEven = All("e", entryType, Imp(Member(e, marked), Equal(sum, D(0))));
        var rowZero = All("e", entryType, Imp(Member(e, marked),
            Equal(Apply(Call("prefixWord", m, row), Call("second", e)), F.Id("false"))));
        var relation = Lambda("a", entryType, Lambda("b", entryType,
            Le(Add(m, Call("mark", b)), Add(k, Call("mark", a)))));
        var seams = Call("IsChain", relation, marked);
        var root = All("e", entryType, Imp(Member(e, Call("headOption", marked)),
            Or(Lt(Add(s, mark), k), Equal(Apply(row, D(0)), D(0)))));
        var n = F.Id("N"); var source = F.Id("source");
        var localBlocks = All("b", nat, Imp(Le(Multiply(Add(b, D(1)), m), n),
            Call("DBonacciAdmissible", k, m,
                Lambda("i", Call("Fin", m), Apply(source,
                    Index(Add(Multiply(b, m), Call("val", i)), n))))));
        var witness = Exists("N", nat, Exists("source", Arrow(Call("Fin", n), bit), And(
            Divides(m, n), Call("DBonacciAdmissible", k, n, source),
            Equal(Call("runBits", k, source, start), current),
            Equal(Call("originalWordValue", k, source), v),
            Equal(Call("tailAfter", D(0), source), s), localBlocks,
            Equal(Call("fixedBlockArchive", actions, Call("runBits", k, source, start)), predicted))));
        var shared = All("k", nat, All("m", nat, All("alphabet", bit,
            All("marked", Call("List", entryType), All("v", scalar, All("j", group, All("s", nat,
                Imp(And(Le(D(3), k), Le(D(1), m), Lt(m, k), rowEven, rowZero, seams,
                    Lt(s, k), root,
                    Divides(Call("gcd", m, Add(k, D(1))), Call("val", new Formula.Negate(j)))),
                    And(Equal(Call("length", actions), Call("length", marked)),
                        Equal(archive, predicted),
                        Equal(Call("length", archive), Call("length", marked)),
                        new Formula.Not(Member(F.Id("none"), archive)), witness)))))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A zero inside each complete word controls the inherited run across its next seam.",
            H("Internal zeros and literal seam safety"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("internal-zero-execution"),
                    DeclarationHandle.Create(Owner + "internal_zero_execution"),
                    H("Internal zero execution"),
                    StatementSource.FromAuthor(Disp(execution)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The word has m<k bits and a marked zero at position i. If the "
                        + "incoming tail plus i is below k, every bit before that mark is "
                        + "safe. Alternatively a zero at the first position clears any "
                        + "legal inherited tail. The marked zero makes the terminal tail "
                        + "independent of the incoming tail and bounds it by m-1-i. "
                        + "The scalar and phase are those of the original literal executor. "
                        + "The bound uses the mark, so later seams may have two adjacent "
                        + "one bits. It does not require a zero at either block boundary.")),
                        Paragraph(Text(
                            "Subtraction in the tail bound is natural subtraction. "
                            + "The index i:Fin(m) already implies m>0. Only the complete "
                            + "endpoint is observed; the internal zero is a literal bit "
                        + "of the paid word."))), DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("actual-internal-zero-charge-suffix"),
                    DeclarationHandle.Create(Owner + "actual_internal_zero_charge_suffix"),
                    H("One common literal suffix"),
                    StatementSource.FromAuthor(Disp(shared)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "An entry is a pair consisting of an ordered charge row and a "
                        + "marked Fin(m) position. Here row(e) is its first projection, "
                        + "second(e) its second projection, mark(e) the natural value of "
                        + "that position, and mapFirst(marked)=marked.map(Prod.fst). "
                        + "chargeBlocks omits the proof arguments 2<=k and m<k in the "
                        + "display. IsChain applies the displayed relation only to "
                        + "consecutive entries. headOption denotes List.head?.")),
                        Paragraph(Text(
                            "Every row is even and its prefix-parity word is zero at "
                            + "the marked position. For adjacent marks a,b the gap bound "
                            + "m+mark(b)<=k+mark(a) makes the outgoing tail from a safe "
                            + "up to b. The first word also satisfies the stated incoming "
                            + "condition. Thus the one common list of words gives exactly "
                            + "chargeArchive, with one completed live reading for every "
                            + "issued block. Its relative phase changes by minus m each "
                            + "time, so the charge windows follow their actual chronology.")),
                        Paragraph(Text(
                            "The source witness realizes the value, phase and inherited "
                            + "tail jointly using original weights and legal complete "
                            + "history blocks. The same suffix works in either alphabet. "
                            + "This uses "), Ref(
                            "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel"),
                            Text(" and the row inverse in "), Ref(
                            "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse"),
                            Text(". The theorem supplies physical safety and the whole "
                            + "archive. It does not construct the charge rows, distinguish "
                            + "phase labels, synthesize stopping or decoding, or establish "
                            + "an adaptive-to-preset price inequality."))), DescribeRole.Theorem))));
    }
}
