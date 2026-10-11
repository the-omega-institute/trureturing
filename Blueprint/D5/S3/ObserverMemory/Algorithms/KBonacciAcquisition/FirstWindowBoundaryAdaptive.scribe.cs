using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class FirstWindowBoundaryAdaptiveDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAdaptive.";
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N")));
        var m = F.Id("m"); var k = Subtract(Multiply(D(2), m), D(2));
        var scalar = Call("ZMod", D(2)); var phase = Call("ZMod", Add(k, D(1)));
        var y = F.Id("Y"); var alphabet = F.Id("alphabet"); var support = F.Id("H");
        var A = F.Id("A"); var B = F.Id("B"); var f = F.Id("f");
        var v = F.Id("v"); var j = F.Id("j"); var s = F.Id("s"); var h = F.Id("h");
        var d = F.Id("d"); var history = F.Id("history"); var issued = F.Id("issued");
        var initial = Call("some", Seq(Langle, Sp, v, Comma, new Formula.Negate(j), Comma, s, Rangle));
        var inside = All("v", scalar, All("h", nat,
            Imp(Call("Member", h, Apply(support, v)), And(Le(D(1), h), Le(h, m)))));
        var distinct = All("v", scalar, new Formula.Not(Eq(Apply(A, v), Apply(B, v))));
        var target = All("v", scalar, All("j", phase, All("s", nat,
            Imp(Lt(s, k), Eq(Apply(f, initial),
                Call("ifThenElse", Call("Member", Call("val", j), Apply(support, v)), Apply(B, v), Apply(A, v)))))));
        var words = Call("flattenAllowedHistory", history);
        var q = Call("OriginalRecord", k, words); var free = Call("output", k, words);
        var selector = Call("adaptiveSelector", m, support, A, B, Apply(f, Call("none")));
        var cost = Call("worstCost", support); var own = Call("sourceCost", support, q);
        var histories = All("history", Call("List", Call("AllowedBlock", k, m, alphabet)),
            Exists("issued", Call("Archive", m), And(
                Call("PaidTrace", selector, free, q, Call("EmptyList"), issued, Apply(f, q)),
                Eq(Call("mapWords", issued), Call("sourceBinaryWords", m, support, q)),
                Eq(Call("length", issued), own),
                Eq(Call("length", Call("archiveWords", issued)), Multiply(m, own)),
                new Formula.Not(Call("Member", Call("none"), Call("mapReplies", issued))))));
        var worstSource = Call("some", Seq(Langle, Sp, v, Comma, D(0), Comma, D(0), Rangle));
        var worst = Exists("v", scalar, Exists("history", Call("List", Call("AllowedBlock", k, m, alphabet)),
            Exists("issued", Call("Archive", m), And(Eq(q, worstSource),
                Call("PaidTrace", selector, Call("some", v), worstSource, Call("EmptyList"), issued, Apply(f, worstSource)),
                Eq(Call("length", issued), cost),
                Eq(Call("length", Call("archiveWords", issued)), Multiply(m, cost))))));
        var bitBudgets = All("b", nat, Iff(Call("AdaptiveBitFeasible", m, alphabet, f, F.Id("b")),
            Le(Multiply(m, cost), F.Id("b"))));
        var result = And(Eq(Call("GlobalAdaptivePrice", k, m, alphabet, f), Call("natCast", cost)),
            All("d", nat, Iff(Call("OriginalAdaptiveFeasible", k, m, alphabet, f, d), Le(cost, d))),
            Call("SelectorLegal", k, alphabet, selector),
            Eq(Apply(selector, Call("none"), Call("EmptyList")), Call("inl", Apply(f, Call("none")))), histories, worst, bitBudgets);
        var statement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", F.Id("Bool"),
            All("H", Arrow(scalar, Call("Finset", nat)), All("A", Arrow(scalar, y),
            All("B", Arrow(scalar, y), All("f", Arrow(Call("Option", Call("LiveRecord", k)), y),
            Imp(And(Le(D(5), m), inside, distinct, target), result))))))));
        var supportCost = Call("binaryCost", F.Id("J"));
        var costFormula = Eq(supportCost, Call("ifThenElse", Eq(F.Id("J"), Call("Empty")), D(0),
            Call("ifThenElse", Call("Even", Call("card", F.Id("J"))), D(1), D(2))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Safe original binary branches stop and pay at their own lengths.",
            H("Independent binary support branches on the full original source"),
            Blocks(Describe.Lean(DescribeId.Create("original-first-window-adaptive-price"),
                DeclarationHandle.Create(Owner + "original_first_window_adaptive_price"),
                H("The exact adaptive budget and chronological fees"),
                StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix m>=5, k=2m-2 and T=2m-1. The output universe is arbitrary, with separately "
                        + "distinct labels at each free value and arbitrary cross-value coincidences. The support may differ "
                        + "between free values. Every INITIAL phase and inherited tail remains in scope, and the legal or "
                        + "rejected history and its length remain unknown.")),
                    Paragraph(Text("For a finite support J the branch fee is the length of that branch’s binary word list. The optimal adaptive budget is max(binaryCost(H(0)), binaryCost(H(1))). "
                            + "The remembered free value chooses the branch once. The selector stops when that branch's "
                            + "own list has ended; it emits no word belonging to the longer branch.")),
                    Paragraph(Text("The decoder compares the acquired consecutive endpoint differences with the binary "
                        + "codes at actual phases. Code equality preserves membership in that branch's support. Empty supports "
                        + "have empty scripts and stop immediately; the independent bottom label also stops without a block. "
                        + "For every actual history, the paid trace contains exactly the selected binary words, and its block "
                        + "and bit lengths are binaryCost(H(v)) and m*binaryCost(H(v)) when the INITIAL record is live, "
                        + "and zero when it is bottom.")),
                    Paragraph(Text("The lower bound applies the zero-block and nonempty one-block necessities at each "
                        + "arbitrary remembered value. The auxiliary target agrees with the original target on that same "
                        + "actual fibre, so neither a value-zero-only root lemma nor a shared branch length is assumed. "
                        + "All issued words are complete length-m blocks and are legal in either original alphabet since m<k.")),
                    Paragraph(Text("The binary code, inverse words, boundary compensation and full-tail safety come from "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/FirstWindowBoundaryAttainment"),
                        Text(". The script selector uses the existing branch stream and stopping definitions at "),
                        Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NearCriticalGrid"),
                        Text(". Each branch is transported through original_final_script and trace_congr, with its own "
                            + "actual INITIAL record and own chronological archive; the constant-length grid trace lemma "
                            + "does not supply the unequal stopping lengths.")),
                    Paragraph(Text("The exact bit budget is m times the block budget. A maximizing value is selected, and the whole-source realization theorem supplies one actual history with INITIAL phase and tail zero at that value. The same history and issued archive attain both worst fees. The adaptive classification is the stated individual-fibre supplier applied to the "
                        + "two free values. The retained relation here is its exact original-history implementation with "
                        + "independent branch stops. The common-stream GLOBAL law and its expanded four-label parity "
                        + "table are separate statements."))), DescribeRole.Theorem))));
    }
}
