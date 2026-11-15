using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233261LiteralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233261Literal.";
    private const string LeanPrefix = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal.";
    private const string OriginalName = "Number of 6Xn 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabeled 6-colorings with no clashing color pairs).";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal six-row complementary-pair arrays with horizontal and antidiagonal bonds.",
        H("Six-row antidiagonal arrays"), Blocks(
            Paragraph(Text("An array is a function from Fin 6 times Fin n to Fin 6. "
                + "A bond joins (r,j) to (s,j+1) exactly when r=s or r.val=s.val+1. "
                + "It excludes equal colours and colours whose values sum to five. "
                + "The first entry is zero. The rank r.val*n+j.val defines the strict "
                + "row-major predecessor relation. No colour is required to occur.")),
            Node("normal", "Strict row-major normalization", NormalFormula(), false, true),
            Node("Legal", "Literal array predicate", LegalFormula(), false, true),
            Node("a", "Literal finite count", CountFormula(), false, true),
            Node("Proper", "Proper pair-label pattern", ProperFormula(), false, false),
            Node("L", "Labelled three-colour count", LabelCountFormula(), false, false),
            Node("counting_bridge", "Exact complementary-pair count", BridgeFormula(), true, false),
            Paragraph(Text("The pair labels identify {0,5}, {1,4}, and {2,3}. "
                + "Canonical first occurrences fix the pair names and the first side "
                + "of each used pair. A pattern with k used pairs has 2^(6*n-k) lifts. "
                + "At width at least two, every proper pattern uses two or three labels, "
                + "and every orbit under label permutations has six members. When one "
                + "label is omitted, the common neighbours of consecutive rows force "
                + "each column to be constant, including the last column. The two "
                + "remaining labels alternate with column parity. Exactly one such "
                + "pattern is canonical. Summing the two possible lift weights gives "
                + "the displayed identity.")),
            Node("result", "The ten-lag integer recurrence", RecurrenceFormula(), true, true),
            Paragraph(Text("A column has six independent pair labels. Its 729 raw states have "
                + "exactly the horizontal and antidiagonal transitions in the literal array. "
                + "The sparse successor lists are checked against all raw column pairs. "
                + "The seventeen tabulated right vectors are checked successive powers on the "
                + "all-ones vector. Their degree-ten identity after six transitions is propagated "
                + "by arbitrary further matrix powers. The polynomial vanishes at one, preserving "
                + "the constant correction six. Scaling lag j by 64^j and cancelling 48 gives "
                + "the stated integer recurrence at every n greater than sixteen. "
                + "All lagged widths are at least seven.")),
            Paragraph(Text("At width one there are no bonds. The count remains the literal "
                + "finite function count; the displayed bridge is asserted only at widths at least "
                + "two. Absent colours remain allowed throughout. The recurrence has no premise "
                + "about computation, finite cutoffs, or the occurrence of all colours.")),
            Paragraph(Text("Proof classification: counting_bridge and result are both bind-only. "
                + "The live consumer of counting_bridge is scale_recurrence, which feeds result. "
                + "The structural two-label arguments are finite transports of the existing "
                + "HardinA233258Strip.columns_constant and HardinA233177Ladder.two_label_classification "
                + "suppliers; the unchanged proof repeats those arguments rather than importing "
                + "an adapter. The transfer propagation directly reuses TransferMatrix.tabulatedPowers "
                + "and TransferMatrix.scalarRelationShift. No escape witness or new general method "
                + "is claimed. The result's proposed admission_basis is open-problem-resolution "
                + "for the complete external assertion, with counting_bridge a consumed auxiliary.")),
            Paragraph(Text("Problems/hardin233261.md gives the complete event, its clause-by-clause "
                + "correspondence and Triage. Its immutable event identifier is "
                + "932336f06d425b3988e1c636ab6db5275e017dd94af2eccba1f0f52fb052d93f; "
                + "the preregistration is https://github.com/the-omega-institute/trureturing/issues/28857 "
                + "and the fixed event is in comment 6768941004. The Proved claim concerns this "
                + "whole event, including the literal finite-count definitions, not a finite prefix. "
                + "Library/Automata/hardin2013a233261.md records the source and literature limits. "
                + "Worldwide continued openness, priority and originality are unverified.")),
            Paragraph(Text("The counting_bridge and result information-escape bindings remain "
                + "declared_unresolved: IE-C050 ClosedTruthReadout reason=unclassified_form "
                + "rule=source.residual_requires_open, empty site/readout, certificate=null and "
                + "escape_from=null. Their compiled Reg attempts do not supply validated bindings. "
                + "The unfinished-audit disclosure is "
                + "https://github.com/the-omega-institute/trureturing/issues/28857#issuecomment-6771906994. "
                + "Independent admission confirmation and canonical freezing remain pending.")),
            Paragraph(Text("Source: R. H. Hardin, OEIS A233261, revision 8, "
                + "https://oeis.org/A233261. Source licensing: https://oeis.org/LICENSE. "
                + "The source calls the recurrence Empirical; no literature priority claim is made.")))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(literature && !theorem ? OriginalName : title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition,
            openProblemResolutionClaim: name == "result"
                ? new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233261"), ResolutionKind.Proved)
                : null);
    private static Formula BridgeFormula()
    {
        var n = V("n");
        return All("n", Q("Nat"), Imp(Le(D(2), n), Eq(
            Mul(D(4,8), Typed(Own("a", n), Q("Int"))),
            Mul(Power(Typed(D(6,4), Q("Int")), n),
                Add(Typed(Own("L", n), Q("Int")), D(6))))));
    }
    private static Formula ProperFormula()
    {
        var n=V("n"); var p=V("P"); var j=V("j"); var h=V("h"); var r=V("r"); var s=V("s");
        var cells=Product(Fin(D(6)),Fin(n));
        var adjacent=Or(Eq(r,s),Eq(Val(r),Add(Val(s),D(1))));
        var next=Typed(Call("Fin.mk",Add(Val(j),D(1)),h),Fin(n));
        var bonds=All("j",Fin(n),All("h",Lt(Add(Val(j),D(1)),n),
            All("r",Fin(D(6)),All("s",Fin(D(6)),Imp(adjacent,Ne(App(p,Pair(r,j)),App(p,Pair(s,next))))))));
        return All("n",Q("Nat"),All("P",Arrow(cells,Fin(D(3))),Eq(Own("Proper",p),Parenthesized(bonds))));
    }
    private static Formula LabelCountFormula()
    {
        var n=V("n"); var p=V("P"); var arrays=Arrow(Product(Fin(D(6)),Fin(n)),Fin(D(3)));
        return All("n",Q("Nat"),Eq(Own("L",n),Call("Finset.card",
            Call("Finset.filter",Fn("P",arrays,Own("Proper",p)),Q("Finset.univ")))));
    }
    private static Formula RecurrenceFormula()
    {
        var n=V("n");
        Formula A(int k) => Typed(Own("a",Call("Int.toNat",k==0 ? n : Sub(n,Num(k)))),Q("Int"));
        var rhs = Mul(Dec("1984"), A(1));
        rhs = Sub(rhs, Mul(Dec("1282048"), A(2)));
        rhs = Add(rhs, Mul(Dec("346292224"), A(3)));
        rhs = Sub(rhs, Mul(Dec("27028094976"), A(4)));
        rhs = Sub(rhs, Mul(Dec("6584184864768"), A(5)));
        rhs = Add(rhs, Mul(Dec("1907721393668096"), A(6)));
        rhs = Sub(rhs, Mul(Dec("214149680718675968"), A(7)));
        rhs = Add(rhs, Mul(Dec("12624715655426342912"), A(8)));
        rhs = Sub(rhs, Mul(Dec("384499321786383466496"), A(9)));
        rhs = Add(rhs, Mul(Dec("4759259971017064316928"), A(10)));
        return All("n",Q("Int"),Imp(Lt(Num(16),n),Eq(A(0),rhs)));
    }

    private static Formula NormalFormula()
    {
        var n = V("n"); var a = V("A"); var p = V("p"); var q = V("q");
        var cells = Product(Fin(D(6)), Fin(n));
        Formula Rank(Formula x) => Add(Mul(Val(Call("Prod.fst", x)), n),
            Val(Call("Prod.snd", x)));
        Formula Earlier(byte colour) => Ex("q", cells,
            And(Lt(Rank(q), Rank(p)), Eq(App(a, q), Typed(D(colour), Fin(D(6))))));
        var current = App(a, p);
        var condition = All("p", cells, And(
            Imp(Or(Eq(current, Typed(D(2), Fin(D(6)))),
                Or(Eq(current, Typed(D(3), Fin(D(6)))),
                    Eq(current, Typed(D(4), Fin(D(6)))))), Earlier(1)),
            Imp(Eq(current, Typed(D(3), Fin(D(6)))), Earlier(2))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Own("normal", a), Parenthesized(condition))));
    }

    private static Formula LegalFormula()
    {
        var n = V("n"); var a = V("A"); var j = V("j");
        var r = V("r"); var s = V("s"); var h = V("h");
        var cells = Product(Fin(D(6)), Fin(n));
        var first = Ex("j", Fin(n),
            And(Eq(Val(j), D(0)), Eq(App(a, Pair(Typed(D(0), Fin(D(6))), j)),
                Typed(D(0), Fin(D(6))))));
        var adjacent = Or(Eq(r, s), Eq(Val(r), Add(Val(s), D(1))));
        var here = App(a, Pair(r, j));
        var next = App(a, Pair(s, Typed(Call("Fin.mk", Add(Val(j), D(1)), h), Fin(n))));
        var bonds = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(6)), All("s", Fin(D(6)), Imp(adjacent,
                And(Ne(here, next), Ne(Add(Val(here), Val(next)), D(5))))))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Own("Legal", a), Parenthesized(And(first, And(bonds, Own("normal", a)))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Fin(D(6)), Fin(n)), Fin(D(6)));
        return All("n", Q("Nat"), Eq(Own("a", n), Call("Finset.card",
            Call("Finset.filter", Fn("A", arrays, Own("Legal", a)), Q("Finset.univ")))));
    }

    private static Formula Dec(string digits) => Seq(digits.Select(c => D((byte)(c - '0'))).ToArray());
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
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
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
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
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
}
