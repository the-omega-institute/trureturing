using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class WindowChargeInverseDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.";

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

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

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

    private static Formula Index(Formula value, Formula bound) =>
        Seq(Langle, Sp, value, Rangle, Underscore, Grp(bound));

    private static Formula Sum(Formula bound, Formula row) =>
        Seq(F.Sum, Underscore, Grp(Seq(F.Id("h"), InMacro, Sp, Call("range", bound))),
            Sp, Apply(row, F.Id("h")));

    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Open, LambdaLower, Sp, Open, F.Id(name), Colon, type, Close, Comma, Sp, body, Close);

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var bit = F.Id("Bool");
        var scalar = Call("ZMod", D(2));
        var k = F.Id("k"); var m = F.Id("m"); var q = F.Id("q");
        var j = F.Id("j"); var rows = F.Id("rows"); var a = F.Id("alphabet");
        var v = F.Id("v"); var s = F.Id("s"); var actions = F.Id("actions");
        var phase = Call("ZMod", Add(k, D(1)));
        var rowType = Arrow(nat, scalar);
        var word = Call("prefixWord", m, q);
        var first = Apply(word, Index(D(0), m));
        var last = Apply(word, Index(Subtract(m, D(1)), m));
        var w = F.Id("w");
        var unique = All("w", Arrow(Call("Fin", m), bit),
            Imp(All("j", phase, Equal(Call("wordIncrement", k,
                new Formula.Negate(j), w), Call("windowCharge", k, m, q, j))), Equal(w, word)));
        var inverse = All("k", nat, All("m", nat, All("q", rowType,
            Imp(And(Le(D(3), k), Le(D(1), m), Lt(m, k), Equal(Sum(Add(m, D(1)), q), D(0))),
                And(All("j", phase, Equal(Call("wordIncrement", k,
                    new Formula.Negate(j), word), Call("windowCharge", k, m, q, j))),
                    Iff(Equal(first, F.Id("false")), Equal(Apply(q, D(0)), D(0))),
                    Iff(Equal(last, F.Id("false")), Equal(Apply(q, m), D(0))), unique)))));

        var current = Call("some", Seq(Open, v, Comma, new Formula.Negate(j), Comma, s, Close));
        var start = Call("some", Seq(Open, D(0), Comma, D(0), Comma, D(0), Close));
        var archive = Call("fixedBlockArchive", actions, current);
        var predicted = Call("chargeArchive", k, m, rows, v, j);
        var incoming = All("q", rowType, Imp(Member(q, Call("headOption", rows)),
            Or(Equal(s, D(0)), Equal(Apply(q, D(0)), D(0)))));
        var n = F.Id("N"); var source = F.Id("source"); var b = F.Id("b"); var i = F.Id("i");
        var sourceRun = Call("runBits", k, source, start);
        var localBlocks = All("b", nat, Imp(Le(Multiply(Add(b, D(1)), m), n),
            Call("DBonacciAdmissible", k, m,
                Lambda("i", Call("Fin", m),
                    Apply(source, Index(Add(Multiply(b, m), Call("val", i)), n))))));
        var joint = Exists("N", nat, Exists("source", Arrow(Call("Fin", n), bit),
            And(Divides(m, n), Call("DBonacciAdmissible", k, n, source),
                Equal(sourceRun, current), Equal(Call("originalWordValue", k, source), v),
                Equal(Call("tailAfter", D(0), source), s), localBlocks,
                Equal(Call("fixedBlockArchive", actions, sourceRun), predicted))));
        var suffixConclusion = And(Equal(Call("length", actions), Call("length", rows)),
            Equal(archive, predicted), Equal(Call("length", archive), Call("length", rows)),
            new Formula.Not(Member(F.Id("none"), archive)), joint);
        var letActions = Seq(Operatorname, Grp(F.Id("let")), Sp, actions, Eq,
            Call("chargeBlocks", k, m, a, rows), Sp, Operatorname, Grp(F.Id("in")), Sp,
            Open, suffixConclusion, Close);
        var suffix = All("k", nat, All("m", nat, All("alphabet", bit,
            All("rows", Call("List", rowType), All("v", scalar, All("j", phase, All("s", nat,
                Imp(And(Le(D(3), k), Le(D(1), m), Lt(m, k), Call("safeRows", m, rows),
                    Lt(s, k), incoming,
                    Divides(Call("gcd", m, Add(k, D(1))), Call("val", new Formula.Negate(j)))),
                    letActions))))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Prefix-parity inverses realize short-window charges by actual shared endpoint words.",
            H("Literal inverses and safe shared charge suffixes"),
            Blocks(
            Describe.Lean(
                DescribeId.Create("charge-inverse-short-legal"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.short_legal"),
                H("Short words are legal in either alphabet"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k at least two and m less than k, every complete m-bit word is DBonacciAdmissible. Both the exceptional first-zero execution and the fixed suffix use this internal admissibility."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charge-inverse-short-safe-execution"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/WindowChargeInverse.short_safe_execution"),
                H("A cleared incoming seam succeeds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a valid incoming tail and a short nonempty word, either incoming tail zero or literal first bit zero gives the exact successful native scalar, phase and tail updates. The terminal tail equals its zero-tail evaluation and remains below k. For the exceptional first word, its actual first bit is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("window-charge-bit-scalar"),
                DeclarationHandle.Create(Owner + "bitScalar"),
                H("Literal bit scalars"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A true literal bit contributes one in ZMod 2; a false bit contributes zero."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("window-charge-extended-bit"),
                DeclarationHandle.Create(Owner + "extendedBit"),
                H("The zero extension of one word"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Offsets inside the word carry that literal bit scalar; all offsets beyond the word carry zero."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("window-charge-increment-derivative"),
                DeclarationHandle.Create(Owner + "increment_derivative"),
                H("The native ordered adjacent-bit charge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k at least three and a word shorter than k, its original matched scalar increment at negative phase j is the sum of the bit scalar at offset j and its predecessor, with zero extension at both ends. The formula applies to every modular phase."))), DescribeRole.Theorem),
                Paragraph(Text(
                    "The reader uses the original integer KBonacci weights and the matched scalar "
                    + "in ZMod(2). The period is k+1. A row q is a function from natural offsets "
                    + "to ZMod(2); only offsets zero through m are used. The literal word "
                    + "prefixWord(m,q) has bit i equal to the decision that the sum of q(h) "
                    + "over h<i+1 is nonzero. windowCharge(k,m,q,j) is q(val(j)) when val(j)<=m "
                    + "and zero otherwise. All row sums and scalar differences are in ZMod(2).")),
                Describe.Lean(
                    DescribeId.Create("short-window-charge-inverse"),
                    DeclarationHandle.Create(Owner + "short_window_charge_inverse"),
                    H("An even ordered window has a physical prefix-parity inverse"),
                    StatementSource.FromAuthor(Disp(inverse)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For k>=3 and 1<=m<k, the prescribed even row is exactly the "
                            + "native increment of this m-bit word at every ambient phase -j, "
                            + "including zero increment outside the ordered window. Its first "
                            + "bit is zero exactly when q(0)=0, and its last bit is zero exactly "
                            + "when q(m)=0. Every m-bit word with these same increments at "
                            + "all phases equals prefixWord(m,q). A displayed angle index with "
                            + "value r and subscript n denotes the Fin(n) element of value r, "
                            + "with its proof r<n supplied by the hypotheses. No phase reading "
                            + "is used to choose the word.")),
                        Paragraph(Text("The adjacent coefficient and marker identities of "),
                            Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonLower"),
                            Text(" evaluate the literal increment. Prefix cancellation then "
                                + "recovers every row entry, with the final entry supplied by "
                                + "the even total charge."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("actual-shared-charge-suffix"),
                    DeclarationHandle.Create(Owner + "actual_shared_charge_suffix"),
                    H("One literal suffix realizes every row on each joint actual source"),
                    StatementSource.FromAuthor(Disp(suffix)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "safeRows(m,rows) requires each row to have even total charge. "
                            + "For successive rows q and r it also requires q(m)=0 or r(0)=0. "
                            + "The first row requires a cleared incoming tail or q(0)=0. "
                            + "headOption is the optional head, with no member for an empty list. "
                            + "chargeBlocks maps the rows to the very prefixWord words, as "
                            + "allowed complete blocks for alphabet; its proof arguments "
                            + "2<=k and m<k are omitted in the displayed applications. This "
                            + "one list depends on the rows and the reader, and is shared by "
                            + "all values, phases, tails and response children.")),
                        Paragraph(Text(
                            "chargeArchive is empty for an empty row list. For q::rest, "
                            + "put next=v+windowCharge(k,m,q,j); its archive is some(next) "
                            + "followed by chargeArchive(k,m,rest,next,j-m). This is exactly "
                            + "the native complete-endpoint archive, of length rows.length "
                            + "with no rejected endpoint. Each of its words has m literal "
                            + "bits and costs one issued complete block. An all-one word "
                            + "is included when its incoming tail has been cleared.")),
                        Paragraph(Text(
                            "The endpoint subgroup condition supplies one legal complete-block "
                            + "source realizing value v, phase -j and tail s simultaneously. "
                            + "Its original-weight scalar is v, every constituent source block "
                            + "is internally legal, and appending this same suffix gives the "
                            + "same predicted archive. This uses "),
                            Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/LiteralModel"),
                            Text(" and the native archive of "),
                            Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/EndpointCells"),
                            Text(". The history witness proves joint reachability; it provides "
                                + "no reset, copied source, free padding or intermediate reading.")),
                        Paragraph(Text(
                            "At an acquired child with current phase -jINITIAL+(a+1)m, the "
                            + "relative index in this statement is jINITIAL-(a+1)m. Each later "
                            + "row therefore acts at its actual chronological index. This "
                            + "coordinate calculation does not reveal the INITIAL phase. "
                            + "A decoder must still return the INITIAL label, rather than a "
                            + "label of the updated record. The result supplies "
                            + "the physical inversion and the seams with an adjacent zero; "
                            + "it does not select label codes, prove a decoder, handle a "
                            + "seam whose adjacent bits are both one, or assert a minimum "
                            + "fee for a full INITIAL target."))),
                    DescribeRole.Theorem))));
    }
}
