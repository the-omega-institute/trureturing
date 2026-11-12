using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA202330Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/hardinbarker2018a202330");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All labeled four-column Boolean arrays whose consecutive two-bit windows are nondecreasing in every row and column.",
        H("Increasing two-bit windows: A202330"),
        Blocks(
            Node("bit", "Integer bit values", "bit", Disp(All("b", Op("Bool"), Eq(Call("bit", V("b")), IfF(Eq(V("b"), Op("true")), Num(1), Num(0))))), "A Boolean bit is mapped into the integers before addition or multiplication.", DescribeRole.Definition),
            Node("horizontal", "Horizontal windows", "horizontal", HorizontalFormula(), "The two comparisons use positions 0,1,2 and 1,2,3. Their window values are ordinary binary integers.", DescribeRole.Definition),
            Node("valid", "The native array predicate", "valid", ValidFormula(), "Every row satisfies both horizontal comparisons. In each column every three consecutive rows satisfy the same inequality. Coordinates and row order are retained; all boundaries are open.", DescribeRole.Definition),
            Node("count", "Native cardinality", "count", CountFormula(), "The count is the cardinality of all labeled functions on the source coordinates satisfying valid. No sorting, symmetry quotient or value computed from the formula defines the count.", DescribeRole.Definition),
            Node("series", "Zero-constant formal series", "generatingSeries", Disp(Eq(V("generatingSeries"), App(Qualified("PowerSeries", "mk"), Fn("n", NatF(), IfF(Eq(V("n"), Num(0)), Num(0), Cast(Call("count", V("n")), RatF())))))), "The source offset is 1,1. Positive coefficients are native counts. The coefficient at zero is zero, independently of the native height-one array count.", DescribeRole.Definition),
            Node("claim", "The three source formulas", "claim", Disp(IffF(V("claim"), ClaimBody())), "The empirical quartic and Barker's conjectural generating function and recurrence refer to the same native count. Subtractions in the recurrence take place in the integers, and the formal series has rational coefficients.", DescribeRole.Definition),
            Node("result", "The full counting identity", "result", Disp(ClaimBody()), "The six horizontal rows are 0000,0001,0010,0011,0111,1111. An exact row equivalence retains all 36 ordered pairs, including the incomparable rows 0001 and 0010. The transfer counts have the vector invariant 12 times T to the power m applied to the all-ones vector equals V(m), for every m at least two. Its initial identity and polynomial transition identity prove the quartic by induction; the actual two smaller counts are 36 and 82. The fifth difference gives the signed recurrence. Coefficient comparison, including the zero coefficient, gives the formal generating function.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin-barker-a202330"), ResolutionKind.Proved))), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(DescribeId.Create("hardin-a202330-" + id), DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula), role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula RowType() => Seq(Fin(Num(4)), To, Op("Bool"));
    private static Formula ArrayType(Formula n) => Seq(Parenthesized(Seq(Fin(PlusF(n, Num(1))), Times, Fin(Num(4)))), To, Op("Bool"));
    private static Formula Window(Formula a, Formula b, Formula c) => LeqF(PlusF(Mul(Num(2), Call("bit", a)), Call("bit", b)), PlusF(Mul(Num(2), Call("bit", b)), Call("bit", c)));
    private static Formula HorizontalFormula()
    {
        var r = V("r"); var j = V("j");
        return Disp(All("r", RowType(), IffF(Call("horizontal", r), All("j", Fin(Num(2)), Window(App(r,j), App(r,PlusF(j,Num(1))), App(r,PlusF(j,Num(2))))))));
    }
    private static Formula ValidFormula()
    {
        var n = V("n"); var a = V("a"); var i = V("i"); var j = V("j");
        var vertical = All("i", NatF(), Imp(new Formula.Relation(PlusF(i,Num(2)), FormulaRelationOperator.LessThan, PlusF(n,Num(1))), All("j", Fin(Num(4)), Window(App(a,i,j), App(a,PlusF(i,Num(1)),j), App(a,PlusF(i,Num(2)),j)))));
        return Disp(All("n", NatF(), All("a", ArrayType(n), IffF(Call("valid",a), AndF(All("i", Fin(PlusF(n,Num(1))), Call("horizontal", Fn("j",Fin(Num(4)),App(a,i,j)))),vertical)))));
    }
    private static Formula CountFormula() => Disp(All("n", NatF(), Eq(Call("count",V("n")), App(Qualified("Nat","card"), Seq(OpenBrace,V("a"),Colon,Sp,ArrayType(V("n")),Sp,Mid,Sp,Call("valid",V("a")),CloseBrace)))));
    private static Formula ClaimBody()
    {
        var n = V("n"); var z = Cast(n,IntF()); var X = V("X");
        Formula C(Formula k) => Cast(Call("count",k),IntF());
        var quartic = All("n",NatF(),Imp(LeqF(Num(1),n),Eq(Mul(Num(12),C(n)),PlusF(PlusF(PlusF(PlusF(Pow(z,Num(4)),Mul(Num(16),Pow(z,Num(3)))),Mul(Num(83),Pow(z,Num(2)))),Mul(Num(176),z)),Num(156)))));
        var numerator = Mul(X,Parenthesized(PlusF(Sub(PlusF(Sub(Num(36),Mul(Num(98),X)),Mul(Num(112),Pow(X,Num(2)))),Mul(Num(61),Pow(X,Num(3)))),Mul(Num(13),Pow(X,Num(4))))));
        var series = Seq(Op("let"),Sp,X,Colon,Sp,Call("PowerSeries",RatF()),Colon,F.Eq,Sp,Qualified("PowerSeries","X"),Semi,Sp,Eq(V("generatingSeries"),Mul(numerator,Pow(Pow(Sub(Num(1),X),Num(5)),Num(-1)))));
        var rec = All("n",NatF(),Imp(LeqF(Num(6),n),Eq(C(n),PlusF(Sub(PlusF(Sub(Mul(Num(5),C(Sub(n,Num(1)))),Mul(Num(10),C(Sub(n,Num(2))))),Mul(Num(10),C(Sub(n,Num(3))))),Mul(Num(5),C(Sub(n,Num(4))))),C(Sub(n,Num(5)))))));
        return AndF(quartic,AndF(series,rec));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(int n) => n < 0 ? Seq(Minus, Num(-n)) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Op(owner), Dot, Op(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Fn(string name, Formula type, Formula body) => Seq(Op("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula IfF(Formula cond, Formula yes, Formula no) => Seq(Op("if"), Sp, cond, Sp, Op("then"), Sp, yes, Sp, Op("else"), Sp, no);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula NatF() => Op("Nat");
    private static Formula IntF() => Op("Int");
    private static Formula RatF() => Op("Rat");
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula PlusF(Formula a, Formula b) => Add(a, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);

}
