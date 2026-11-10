using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA185765TransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185765Transfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceComposition/hardin2011a185765");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-column binary arrays and Hardin's trace-avoidance recurrence.",
        H("HardinA185765Transfer"),
        Blocks(
            Node("blockTrace", "The trace of a contiguous block", BlockFormula(),
                "Number of (n+1)X6 binary arrays with no 2X2 subblock trace equal to any horizontal or vertical neighbor 2X2 subblock trace. NAME field, OEIS A185765 revision 9, without page numbering. The block at origin (i,j) uses rows i,i+1 and columns j,j+1. Its entries are cast to natural numbers before Matrix.trace.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Admissible", "Unequal neighboring traces", AdmissibleFormula(),
                "Number of (n+1)X6 binary arrays with no 2X2 subblock trace equal to any horizontal or vertical neighbor 2X2 subblock trace. NAME field, OEIS A185765 revision 9, without page numbering. Adjacent origins differ by one in exactly one coordinate. Arrays have open rectangular boundaries.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The cardinality of labeled arrays", CountFormula(),
                "Number of (n+1)X6 binary arrays with no 2X2 subblock trace equal to any horizontal or vertical neighbor 2X2 subblock trace. NAME field, OEIS A185765 revision 9, without page numbering. The offset is 1,1. The subtype consists of all labeled admissible arrays; no symmetry quotient is taken.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tau", "Block traces in the row encoding", TauFormula(),
                "The finite equivalence finFunctionFinEquiv encodes each six-entry binary row by an element of Fin 64. The trace is blockTrace of the two decoded rows at row origin zero.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("H", "Horizontal comparisons", HorizontalFormula(),
                "Admissible is applied to the two decoded rows. Its vertical condition is vacuous, and its horizontal condition compares the four adjacent block origins.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("V", "Vertical comparisons", VerticalFormula(),
                "The five traces in successive overlapping row pairs must differ coordinatewise.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("step", "One continuation step", StepFormula(),
                "A horizontally valid row pair sums the continuation values at each vertically compatible next row. Invalid row pairs have value zero.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("u", "Continuation counts", UFormula(),
                "The initial vector is one on horizontally valid pairs and zero elsewhere. Each further vector applies step.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("counting_bridge", "Literal arrays and continuation counts", BridgeFormula(),
                "Encoding rows and splitting their finite function space at its first two entries gives this identity. Induction on the remaining rows identifies the finite sum with u.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("tables", "The fifteen integer tables", Seq(F.Id("tables"), Sp, Colon, Sp, Call("Array", Call("Array", Call("Array", Ints)))),
                "The literal array stores fifteen 64 by 64 integer tables, in order from continuation length zero through fourteen. Rows and columns use finFunctionFinEquiv. Entries outside horizontally valid row pairs are zero. The initial table gives horizontal compatibility, and fourteen transitions give the successive continuation counts.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("adjData", "The successor lists", Seq(F.Id("adjData"), Sp, Colon, Sp, Call("Array", Call("Array", Call("List", FinOf(64))))),
                "This literal 64 by 64 array of lists records successor rows. A list at a horizontally valid pair contains exactly the rows satisfying the horizontal and vertical comparisons for the next pair.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("fastStep", "Sparse continuation step", FastFormula(),
                "The sparse sum uses the finite successor set in place of testing all 64 rows.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("table", "Table entries on valid row pairs", TableFormula(),
                "The table at k has the entries of the kth literal integer array on H and is zero elsewhere. Each exclamation-mark array index uses Lean default-value indexing.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("fastStep_table_data", "The sparse transfer evaluated from the integer data", FastTableDataFormula(),
                "Every successor satisfies the horizontal comparisons, so its guarded table entry equals the corresponding integer entry.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("table_base", "The initial table", TableBaseFormula(),
                "The zeroth table agrees with the initial continuation vector at every row pair.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("step_table_fast", "Sparse evaluation of a table", StepTableFormula(),
                "Each table vanishes outside H, so its two transfer steps agree.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("table_step_0", "The transfer from table 0 to 1", TableStepFormula(0),
                "At every row pair, the transfer of the table at 0 equals the table at 1.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("table_step_1", "The transfer from table 1 to 2", TableStepFormula(1),
                "At every row pair, the transfer of the table at 1 equals the table at 2.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("table_step_2", "The transfer from table 2 to 3", TableStepFormula(2),
                "At every row pair, the transfer of the table at 2 equals the table at 3.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("table_step_3", "The transfer from table 3 to 4", TableStepFormula(3),
                "At every row pair, the transfer of the table at 3 equals the table at 4.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("table_step_4", "The transfer from table 4 to 5", TableStepFormula(4),
                "At every row pair, the transfer of the table at 4 equals the table at 5.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("table_step_11", "The transfer from table 11 to 12", TableStepFormula(11),
                "At every row pair, the transfer of the table at 11 equals the table at 12.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("table_step_12", "The transfer from table 12 to 13", TableStepFormula(12),
                "At every row pair, the transfer of the table at 12 equals the table at 13.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("table_step_13", "The transfer from table 13 to 14", TableStepFormula(13),
                "At every row pair, the transfer of the table at 13 equals the table at 14.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hardin-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Fn(string name, Formula type, Formula body) => Seq(Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Arrow(Formula x, Formula y) => Seq(Parenthesized(x), Sp, To, Sp, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula IffTo(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula FinOf(long n) => Call("Fin", Num(n));
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Vectors => Arrow(FinOf(64), Arrow(FinOf(64), Ints));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Sp, Colon, Sp, Ints));
    private static Formula SumBound(string name, Formula type, Formula body) => Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula SumMem(string name, Formula set, Formula body) => Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Index(Formula array, Formula index) => Seq(Parenthesized(array), OpenBracket, index, CloseBracket, Bang);
    private static Formula MatrixType(Formula n) => Call("Matrix", Call("Fin", Add(n, Num(1))), FinOf(6), FinOf(2));
    private static Formula RowEquiv() => Parenthesized(Seq(F.Id("finFunctionFinEquiv"), Sp, Colon, Sp, Call("Equiv", Arrow(FinOf(6), FinOf(2)), FinOf(64))));
    private static Formula BlockFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A"), i = F.Id("i"), j = F.Id("j"), r = F.Id("r"), c = F.Id("c");
        Formula ri = Call("ite", Equal(r, Num(0)), App(Q("Fin", "castSucc"), i), App(Q("Fin", "succ"), i));
        Formula cj = Call("ite", Equal(c, Num(0)), App(Q("Fin", "castSucc"), j), App(Q("Fin", "succ"), j));
        Formula block = Fn("r", FinOf(2), Fn("c", FinOf(2), Val(App(a, ri, cj))));
        return All("n", Nats, All("A", MatrixType(n), All("i", Call("Fin", n), All("j", FinOf(5), Equal(Call("blockTrace", a, i, j), App(Q("Matrix", "trace"), block))))));
    }
    private static Formula AdmissibleFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A"), i = F.Id("i"), h = F.Id("h"), j = F.Id("j"), k = F.Id("k");
        Formula horizontal = All("i", Call("Fin", n), All("j", FinOf(5), All("k", FinOf(5), Imp(Equal(Val(k), Add(Val(j), Num(1))), NotEqual(Call("blockTrace", a, i, j), Call("blockTrace", a, i, k))))));
        Formula vertical = All("i", Call("Fin", n), All("h", Call("Fin", n), All("j", FinOf(5), Imp(Equal(Val(h), Add(Val(i), Num(1))), NotEqual(Call("blockTrace", a, i, j), Call("blockTrace", a, h, j))))));
        return All("n", Nats, All("A", MatrixType(n), IffTo(Call("Admissible", a), And(horizontal, vertical))));
    }
    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A");
        Formula subtype = Seq(OpenBrace, a, Sp, Colon, Sp, MatrixType(n), Sp, Slash, Slash, Sp, Call("Admissible", a), CloseBrace);
        return All("n", Nats, Equal(Call("a", n), App(Q("Nat", "card"), subtype)));
    }
    private static Formula DecodedRows(Formula r, Formula s)
    {
        Formula symm = App(Q("Equiv", "symm"), RowEquiv());
        return App(Q("Fin", "cons"), App(symm, r),
            App(Q("Fin", "cons"), App(symm, s), Q("Fin", "elim0")));
    }
    private static Formula TauFormula()
    {
        Formula r = F.Id("r"), s = F.Id("s"), j = F.Id("j");
        return All("r", FinOf(64), All("s", FinOf(64), All("j", FinOf(5),
            Equal(Call("tau", r, s, j), Call("blockTrace", DecodedRows(r, s), Num(0), j)))));
    }
    private static Formula HorizontalFormula()
    {
        Formula r = F.Id("r"), s = F.Id("s");
        return All("r", FinOf(64), All("s", FinOf(64),
            IffTo(Call("H", r, s), Call("Admissible", DecodedRows(r, s)))));
    }
    private static Formula VerticalFormula()
    {
        Formula r = F.Id("r"), s = F.Id("s"), t = F.Id("t"), j = F.Id("j");
        return All("r", FinOf(64), All("s", FinOf(64), All("t", FinOf(64), IffTo(Call("V", r, s, t), All("j", FinOf(5), NotEqual(Call("tau", r, s, j), Call("tau", s, t, j)))))));
    }
    private static Formula StepFormula()
    {
        Formula v = F.Id("v"), r = F.Id("r"), s = F.Id("s"), t = F.Id("t");
        Formula body = Call("ite", Call("H", r, s), SumBound("t", FinOf(64), Call("ite", Call("V", r, s, t), App(v, s, t), Num(0))), Num(0));
        return All("v", Vectors, All("r", FinOf(64), All("s", FinOf(64), Equal(Call("step", v, r, s), body))));
    }
    private static Formula UFormula()
    {
        Formula k = F.Id("k"), r = F.Id("r"), s = F.Id("s");
        return All("r", FinOf(64), All("s", FinOf(64), And(Equal(Call("u", Num(0), r, s), Call("ite", Call("H", r, s), Num(1), Num(0))), All("k", Nats, Equal(Call("u", Add(k, Num(1)), r, s), Call("step", Call("u", k), r, s))))));
    }
    private static Formula BridgeFormula()
    {
        Formula k = F.Id("k"), r = F.Id("r"), s = F.Id("s");
        return All("k", Nats, Equal(Cast(Call("a", Add(k, Num(1)))), SumBound("r", FinOf(64), SumBound("s", FinOf(64), Call("u", k, r, s)))));
    }
    private static Formula FastFormula()
    {
        Formula v = F.Id("v"), r = F.Id("r"), s = F.Id("s"), t = F.Id("t");
        return All("v", Vectors, All("r", FinOf(64), All("s", FinOf(64), Equal(Call("fastStep", v, r, s), Call("ite", Call("H", r, s), SumMem("t", App(Q("List", "toFinset"), Index(Index(F.Id("adjData"), Val(r)), Val(s))), App(v, s, t)), Num(0))))));
    }
    private static Formula TableFormula()
    {
        Formula k = F.Id("k"), r = F.Id("r"), s = F.Id("s");
        return All("k", Nats, All("r", FinOf(64), All("s", FinOf(64), Equal(Call("table", k, r, s), Call("ite", Call("H", r, s), Index(Index(Index(F.Id("tables"), k), Val(r)), Val(s)), Num(0))))));
    }
    private static Formula FastTableDataFormula()
    {
        Formula k = F.Id("k"), r = F.Id("r"), s = F.Id("s"), t = F.Id("t");
        Formula successors = App(Q("List", "toFinset"), Index(Index(F.Id("adjData"), Val(r)), Val(s)));
        Formula entry = Index(Index(Index(F.Id("tables"), k), Val(s)), Val(t));
        Formula value = Call("ite", Call("H", r, s), SumMem("t", successors, entry), Num(0));
        Formula equality = Equal(Call("fastStep", Call("table", k), r, s), value);
        return All("k", Nats, All("r", FinOf(64), All("s", FinOf(64), equality)));
    }
    private static Formula TableBaseFormula()
    {
        Formula r = F.Id("r"), s = F.Id("s");
        return All("r", FinOf(64), All("s", FinOf(64), Equal(Call("u", Num(0), r, s), Call("table", Num(0), r, s))));
    }
    private static Formula StepTableFormula()
    {
        Formula k = F.Id("k");
        return All("k", Nats, Equal(Call("step", Call("table", k)), Call("fastStep", Call("table", k))));
    }
    private static Formula TableStepFormula(long n)
    {
        Formula r = F.Id("r"), s = F.Id("s");
        return All("r", FinOf(64), All("s", FinOf(64), Equal(Call("step", Call("table", Num(n)), r, s), Call("table", Num(n + 1), r, s))));
    }
}
