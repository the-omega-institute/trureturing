using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LiteralWordNonbacktrackingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LiteralWordNonbacktracking.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A literal group-product trace recovers a walk's length and successive labels; distinct consecutive involutions exclude immediate backtracking.",
        H("Literal Group Traces Exclude Immediate Backtracking"),
        Blocks(
            Paragraph(Text(
                "Let G be a group, V a type, F a simple graph on V and val any function from V to G. "
                + "Let w be an actual F walk from a to b, and word a list of elements of G. "
                + "mapSupport(w,val) is w.support.map(val). scanFrom(val(a),word) is List.scanl with "
                + "step (x,r) mapped to x*r, including the initial value. getVert(w,i) denotes the "
                + "actual vertex at natural position i, and letter(word,i) is the list entry at i "
                + "under the displayed bound. Neither injectivity of val nor a Cayley graph structure "
                + "on F is assumed.")),
            Describe.Lean(DescribeId.Create("literal-trace-length"),
                DeclarationHandle.Create(Prefix + "trace_length"),
                H("The Literal Trace Determines the Walk Length"),
                StatementSource.FromAuthor(LengthFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the mapped full support equals the literal scan, w has exactly as many edges "
                    + "as word has letters. Both lists contain one more entry than those lengths, "
                    + "so equality of their lengths gives the result."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-trace-step"),
                DeclarationHandle.Create(Prefix + "trace_step"),
                H("The Literal Trace Determines Each Group Step"),
                StatementSource.FromAuthor(StepFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every index i below word.length, val(getVert(w,i+1)) is "
                    + "val(getVert(w,i))*letter(word,i). The length identity places both vertices "
                    + "within the support, and the scan's successor equation supplies this step."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-trace-nonbacktracking"),
                DeclarationHandle.Create(Prefix + "trace_nonbacktracking"),
                H("Distinct Consecutive Involutions Exclude Backtracking"),
                StatementSource.FromAuthor(NonbacktrackingFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume the exact full support trace, that each letter x satisfies x*x=1, and "
                    + "that consecutive letters differ. Then the actual vertices at i and i+2 "
                    + "differ whenever i+2 is within w.length. If they coincided, mapping their "
                    + "equality through val and using the two exact steps would give x*y=1. "
                    + "Multiplication by the involutive second letter forces x=y, contradicting "
                    + "the consecutive-letter hypothesis."))), DescribeRole.Theorem),
            Paragraph(Text(
                "This result applies to any actual graph walk with such a trace. It proves exclusion "
                + "of immediate backtracking. Simplicity and complete component coverage require "
                + "additional graph conditions, such as the degree and leaf hypotheses for leaf walks.")))));

    private static Formula LengthFormula() => Quantify(Implies(Trace(),
        Equal(Call("length", F.Id("w")), Call("length", F.Id("word")))));

    private static Formula StepFormula()
    {
        Formula i = F.Id("i"), val = F.Id("val"), w = F.Id("w"), word = F.Id("word");
        return Quantify(Implies(Trace(), All("i", Call("Nat"), Implies(
            Lt(i, Call("length", word)), Equal(
                Call("apply", val, Call("getVert", w, Add(i, D(1)))),
                Mul(Call("apply", val, Call("getVert", w, i)), Call("letter", word, i)))))));
    }

    private static Formula NonbacktrackingFormula()
    {
        Formula i = F.Id("i"), x = F.Id("x"), w = F.Id("w"), word = F.Id("word");
        Formula involutions = All("x", F.Id("G"), Implies(Member(x, word), Equal(Mul(x, x), D(1))));
        Formula labels = All("i", Call("Nat"), Implies(Lt(Add(i, D(1)), Call("length", word)),
            Ne(Call("letter", word, i), Call("letter", word, Add(i, D(1))))));
        Formula result = All("i", Call("Nat"), Implies(Le(Add(i, D(2)), Call("length", w)),
            Ne(Call("getVert", w, i), Call("getVert", w, Add(i, D(2))))));
        return Quantify(Implies(And(Trace(), And(involutions, labels)), result));
    }

    private static Formula Trace() => Equal(Call("mapSupport", F.Id("w"), F.Id("val")),
        Call("scanFrom", Call("apply", F.Id("val"), F.Id("a")), F.Id("word")));
    private static Formula Quantify(Formula body) => Disp(All("G", Call("Type"),
        Seq(OpenBracket, Call("Group", F.Id("G")), CloseBracket, Sp,
            All("V", Call("Type"), All("F", Call("SimpleGraph", F.Id("V")),
                All("val", new Formula.TypeArrow(F.Id("V"), F.Id("G")),
                    All("a", F.Id("V"), All("b", F.Id("V"),
                        All("w", Call("Walk", F.Id("F"), F.Id("a"), F.Id("b")),
                            All("word", Call("List", F.Id("G")), body))))))))));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), op, Seq(Open, right, Close));
}
