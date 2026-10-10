using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class OwnPathChargesDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OwnPathCharges.";
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(params Formula[] clauses) =>
        clauses.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Record(Formula v, Formula j, Formula s) =>
        Call("some", Seq(Langle, Sp, v, Comma, new Formula.Negate(j), Comma, s, Rangle));

    public DocumentDefinition Create()
    {
        var nat = Seq(Mathbb, Grp(F.Id("N"))); var bit = F.Id("Bool");
        var m = F.Id("m"); var k = Subtract(Multiply(D(2), m), D(2));
        var group = Call("ZMod", Add(k, D(1))); var scalar = Call("ZMod", D(2));
        var label = F.Id("Y"); var alphabet = F.Id("alphabet");
        var target = F.Id("f"); var table = F.Id("table"); var pi = F.Id("pi");
        var d = F.Id("d"); var t = F.Id("t"); var j = F.Id("j"); var l = F.Id("l");
        var s = F.Id("s"); var v = F.Id("v"); var c = F.Id("c"); var history = F.Id("history");
        var w = Call("flattenWords", history);
        var sameTable = All("v", scalar, All("j", group, All("s", nat,
            Imp(Lt(s, k), Equal(Apply(target, Record(v, j, s)), Apply(table, j))))));
        var correct = All("history", Call("List", Call("AllowedBlock", k, m, alphabet)),
            Imp(Equal(Call("output", k, w), Call("some", D(0))),
                Exists("c", nat, And(Le(c, d),
                    Equal(Call("execute", k, pi, d, w, Call("some", D(0)), F.Id("nil")),
                        Call("some", Seq(Open, Apply(target, Call("OriginalRecord", k, w)),
                            Comma, c, Close)))))));
        Formula Code(Formula index, Formula phase) => Call("phaseCharges", table, pi, d, index, phase);
        var support = All("t", nat, All("j", group,
            Imp(Lt(m, Call("val", Subtract(j, Multiply(t, m)))), Equal(Code(t, j), D(0)))));
        var separation = All("j", group, All("l", group,
            Imp(All("t", nat, Imp(Lt(t, d), Equal(Code(t, j), Code(t, l)))),
                Equal(Apply(table, j), Apply(table, l)))));
        var statement = All("Y", F.Id("Type"), All("m", nat, All("alphabet", bit,
            All("f", Arrow(Call("Option", Call("LiveRecord", k)), label),
            All("table", Arrow(group, label), All("pi", Call("Selector", m, label), All("d", nat,
                Imp(And(Le(D(5), m), sameTable, correct),
                    And(support, Equal(Code(D(0), D(0)), D(0)), separation)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Chronological own-path differences separate arbitrary INITIAL phase labels.",
            H("Own-path padded charge arrays"), Blocks(
                Describe.Lean(DescribeId.Create("own-charge"),
                    DeclarationHandle.Create(Owner + "ownCharge"), H("Own successful differences"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Starting from the current scalar, phase, tail, remembered "
                        + "free reading and actual archive, ownCharge follows the selector for a finite "
                        + "remaining budget. A successful issued word contributes its literal increment "
                        + "and recurses at the next scalar, phase, tail and completed archive. A stop, "
                        + "exhausted budget or rejection gives zero for all remaining coordinates. "
                        + "The rejection case retires a common-tail candidate archive; correctness "
                        + "will force every INITIAL label in that archive to agree."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("phase-charges"),
                    DeclarationHandle.Create(Owner + "phaseCharges"), H("The full phase array"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For k=2m-2, a constant phase table is retired at the root "
                        + "and has the zero array. Otherwise phaseCharges evaluates ownCharge at "
                        + "INITIAL scalar zero, phase minus j, tail zero, free reading some zero "
                        + "and empty archive. Each phase follows its own acquired path. These finite "
                        + "design coordinates are not extra observations available to a controller."))),
                    DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-adaptive-charge-array"),
                    DeclarationHandle.Create(Owner + "original_adaptive_charge_array"),
                    H("Support, cleared root and label separation"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Y is arbitrary, including higher universes. In the display "
                        + "k abbreviates 2m-2; flattenWords is the original history flatMap of each "
                        + "complete literal word. output, execute and OriginalRecord are the original "
                        + "scanner definitions, with their positive-k proof arguments omitted. nil is "
                        + "the empty acquired archive. Subtraction inside val is in ZMod(k+1), after "
                        + "casting t*m into that group. Natural subtraction in k remains truncated.")),
                        Paragraph(Text("The controller is arbitrary. Its correctness premise covers "
                            + "every actual complete-block history with free reading zero, in either "
                            + "original alphabet, and the target premise retains both scalar values "
                            + "and every legal inherited tail. Coprimality and the joint-history "
                            + "realization supply every phase and tail in that premise. A nonconstant "
                            + "table forbids a leading-one root: tail k-1 would reject all phases into "
                            + "one absorbing native execution. Its first bit is therefore zero and "
                            + "clears every inherited tail. The root phase-zero increment is zero.")),
                        Paragraph(Text("At a successful action, literal legality depends on the "
                            + "common tail and word, not on phase or scalar. The endpoint increment "
                            + "selects the next common-scalar, common-tail archive. Equal padded "
                            + "columns follow the same archive through the earlier stop. A common "
                            + "rejection gives the same absorbing continuation and hence a common "
                            + "label; replacing that continuation by zeros loses no label distinction. "
                            + "The support condition follows the actual chronological phase shift "
                            + "t*m, retaining waits and every issued word at its own index.")),
                        Paragraph(Text("This theorem constructs the supported adaptive design array. "
                            + "Its rows need not have even full-window parity and need not be a common "
                            + "preset word. It establishes no donor correction, phase-separating "
                            + "fallback stream, preset decoder, finite price or four-block inequality."))),
                    DescribeRole.Theorem))));
    }
}
