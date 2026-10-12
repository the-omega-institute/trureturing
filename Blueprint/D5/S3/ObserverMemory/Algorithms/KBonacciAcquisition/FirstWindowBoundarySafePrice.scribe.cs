using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FirstWindowBoundarySafePriceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundarySafePrice.";
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N"))); var m = F.Id("m");
        var k = Subtract(Multiply(D(2), m), D(2));
        var scalar = Call("ZMod", D(2)); var phase = Call("ZMod", Add(k, D(1)));
        var y = F.Id("Y"); var alphabet = F.Id("alphabet"); var support = F.Id("H");
        var A = F.Id("A"); var B = F.Id("B"); var f = F.Id("f");
        var v = F.Id("v"); var j = F.Id("j"); var s = F.Id("s"); var h = F.Id("h");
        var initial = Call("some", Seq(Langle, Sp, v, Comma, new Formula.Negate(j), Comma, s, Rangle));
        var inside = All("v", scalar, All("h", nat,
            Imp(Call("Member", h, Apply(support, v)), And(Le(D(1), h), Le(h, m)))));
        var distinct = All("v", scalar, new Formula.Not(Eq(Apply(A, v), Apply(B, v))));
        var target = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), Eq(Apply(f, initial),
                Call("ifThenElse", Call("Member", Call("val", j), Apply(support, v)), Apply(B, v), Apply(A, v)))))));
        var stream = F.Id("stream"); var stop = F.Id("stop"); var issued = F.Id("issued");
        var selector = Call("presetSelector", stream, stop); var cost = Call("presetCost", m, support);
        var words = Call("flattenAllowedHistory", F.Id("history"));
        var q = Call("OriginalRecord", k, words); var free = Call("output", k, words);
        var own = Call("fee", cost, q); var historyType = Call("List", Call("AllowedBlock", k, m, alphabet));
        var traces = All("history", historyType, Exists("issued", Call("Archive", m),
            And(Call("PaidTrace", selector, free, q, Call("EmptyList"), issued, Apply(f, q)),
                Eq(Call("length", issued), own),
                Eq(Call("length", Call("archiveWords", issued)), Multiply(m, own)),
                new Formula.Not(Call("Member", Call("none"), Call("mapSecond", issued))))));
        var joint = Call("some", Seq(Langle, D(0), Comma, D(0), Comma, D(0), Rangle));
        var worst = Exists("history", historyType, Exists("issued", Call("Archive", m),
            And(Eq(q, joint), Call("PaidTrace", selector, Call("some", D(0)), joint,
                Call("EmptyList"), issued, Apply(f, joint)), Eq(Call("length", issued), cost),
                Eq(Call("length", Call("archiveWords", issued)), Multiply(m, cost)))));
        var result = Exists("stream", Arrow(nat, Arrow(Call("Fin", m), F.Id("Bool"))),
            Exists("stop", Arrow(Call("Option", scalar), Arrow(Call("Archive", m), Call("Option", y))),
                And(Call("SelectorLegal", k, alphabet, selector),
                    Eq(Apply(stop, Call("none"), Call("EmptyList")), Call("some", Apply(f, Call("none")))),
                    traces, worst)));
        var statement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", F.Id("Bool"),
            All("H", Arrow(scalar, Call("Finset", nat)), All("A", Arrow(scalar, y),
            All("B", Arrow(scalar, y), All("f", Arrow(Call("Option", Call("LiveRecord", k)), y),
            Imp(And(Le(D(5), m), inside, distinct, target), result))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "An optimal common literal script remains safe on every original source and has an actual maximizing joint history.",
            H("Safe optimal preset acquisition"), Blocks(Describe.Lean(
                DescribeId.Create("original-first-window-safe-preset-price"),
                DeclarationHandle.Create(Owner + "original_first_window_safe_preset_price"),
                H("One safe common stream and its own exact paid traces"),
                StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix arbitrary universe-polymorphic Y and separately distinct label pairs. Labels from different values may coincide, and the independently observed bottom label is unrestricted. Both original alphabets, every original phase and inherited tail, and every unknown legal or rejected initial history are retained. The support membership image counts each phase once.")),
                    Paragraph(Text("A SafePlan consists of literal words, all-phase chronological endpoint codes, their refinement of the ordered membership pair, and absence of bottom replies. For one image class choose the empty script. For two choose the binary script of the support union; the exact normalization allows either component to be empty. Three classes select the homogeneous or either internal two-label construction precisely when Pi3 holds. Four classes select the normalized safe bijective code assignment precisely when Pi4 holds. Every remaining case selects the pulse/donor three-block script. These are the existing physical constructions, including their exterior donors and safe whole-prefix seams; safety is asserted for the selected inverses.")),
                    Paragraph(Text("The decoder searches the selected all-phase code and uses its own consecutive endpoint differences together with its remembered free value. Code refinement makes its INITIAL output well defined even when three-label classes split across four codes. The common words have exactly presetCost blocks. Every live original history executes that entire safe prefix; initial bottom executes none. The constant-length script bridge transports these exact selected words to a PaidTrace on the same actual source, with issued.length equal to fee(presetCost,q) and archiveWords.length equal to m times that fee. No unissued suffix is charged.")),
                    Paragraph(Text("The maximizing witness is one jointly attained original state (value,phase,tail)=(0,0,0), on one original AllowedBlock history. The same history determines the initial record and its paid trace. Its block and bit fees equal presetCost and m times presetCost. The result supplies a safe attaining selector; the exact lower bounds and bit-budget equivalence are given at "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryPrice"), Text(".")),
                    Paragraph(Text("The physical scripts and refinement laws are reused from "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment"), Text(", "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCodes"), Text(", "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryCompatibility"), Text(" and "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryFourLabels"), Text(". The exact common-length trace transport is reused from "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid"), Text(". Unequal adaptive stops use the separate branch-length law at "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAdaptive"), Text(".")),
                    Paragraph(Text("Section 28 is a direct parameter restriction H0,H1 subset of the internal phases: both boundary memberships are zero. For distinct nonempty supports Pi3 then gives exactly the odd-width two-internal-label exception; a four-label image has at least three internal classes and fails Pi4. No additional specialization theorem is needed. The broader all-k/all-m research target, tail-sensitive INITIAL labels and supports outside the first physical window are outside this result."))),
                DescribeRole.Theorem))));
    }
}
