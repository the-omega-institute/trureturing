using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGeometry;

internal sealed class SingerTracePlaneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGeometry/SingerTracePlane.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGeometry/singer1938projective");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The trace-zero points in the projective plane over a prime field form a cyclic Singer difference set of size p+1. Every nonzero cyclic difference occurs exactly once. Multiplication of indices by two permutes the odd-length cycle, so its inverse image has the same cardinality and difference multiplicities.",
        H("Singer trace planes and cyclic difference sets"), Blocks(
            Node("invariant", "Multiplication has no proper invariant subspace", InvariantFormula(),
                "For an element outside the base field, a subspace preserved by multiplication is either zero or the whole cubic extension. The scalars preserving the subspace form a subalgebra; prime extension degree forces a non-base subalgebra to be the whole field.",
                "no_proper_invariant_subspace", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("intersection", "Distinct trace planes meet in a line", IntersectionFormula(),
                "Trace is surjective, so its kernel is a plane. The kernel of x mapped to Tr(a*x) is another plane for nonzero a. If a is outside the base field, equality of these planes would make the trace kernel invariant under multiplication by a. Their sum has dimension three, and their intersection dimension one.",
                "trace_plane_intersection", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The Singer difference-set parameters", ResultFormula(),
                "Singer (1938), pages 377-385: trace-zero projective points form the cyclic (p^2+p+1,p+1,1) difference set. Primitive powers enumerate projective points. A nonzero cyclic shift corresponds to a scalar outside the base field; the unique projective point of the trace-plane intersection counts its difference multiplicity. The last two clauses identify the trace-square support with the inverse image under doubling and give the same multiplicities. Subtraction and addition in Fin(p^2+p+1) are cyclic operations; val is the canonical natural representative.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))), []));

    private static Formula BaseRange() => QCall("Set", "range", Call("algebraMap", Scalars(), Field()));
    private static Formula Subspace() => Call("Submodule", Scalars(), Field());
    private static Formula Kernel(Formula f) => Seq(Parenthesized(f), Dot, Named("ker"));
    private static Formula ScaledTrace(Formula a) => QCall("LinearMap", "comp", TraceMap(), QCall("LinearMap", "mulLeft", Scalars(), a));
    private static Formula TraceMap() => QCall("Algebra", "trace", Scalars(), Field());
    private static Formula InvariantFormula()
    {
        Formula a = F.Id("a"), w = F.Id("W"), x = F.Id("x");
        Formula invariant = All(x, Field(), Implies(Member(x, w), Member(TimesOf(a, x), w)));
        return Disp(BaseBinder(All(a, Field(), All(w, Subspace(),
            Implies(NotMember(a, BaseRange()), Implies(invariant,
                Or(Equal(w, Qualified("Bot", "bot")), Equal(w, Qualified("Top", "top")))))))));
    }
    private static Formula IntersectionFormula()
    {
        Formula a = F.Id("a"), x = F.Id("x");
        Formula intersection = QCall("Min", "min", Kernel(TraceMap()), Kernel(ScaledTrace(a)));
        Formula carrier = Call("Subtype", Seq(Parenthesized(Seq(x, Colon, Sp, Field())), Sp, Mapsto,
            Sp, Member(x, intersection)));
        return Disp(BaseBinder(All(a, Field(), Implies(NotMember(a, BaseRange()),
            Equal(QCall("Module", "finrank", Scalars(), carrier), F.D(1))))));
    }
    private static Formula TraceZero(Formula i, bool doubled) => Equal(Trace(Power(AlphaValue(),
        doubled ? TimesOf(F.D(2), Value(i)) : Value(i))), F.D(0));
    private static Formula Difference(bool doubled)
    {
        Formula i = F.Id("i"), r = F.Id("r");
        return All(r, Index(), Implies(NotEqual(r, F.D(0)),
            Equal(Count(i, And(TraceZero(i, doubled), TraceZero(PlusOf(i, r), doubled))), F.D(1))));
    }
    private static Formula ResultFormula()
    {
        Formula i = F.Id("i");
        Formula doubling = All(i, Index(), Equivalent(TraceZero(i, true),
            Equal(Trace(Power(AlphaValue(), Value(TimesOf(F.D(2), i)))), F.D(0))));
        Formula body = And(Equal(Count(i, TraceZero(i, false)), PlusOf(P(), F.D(1))),
            And(Equal(Count(i, TraceZero(i, true)), PlusOf(P(), F.D(1))),
                And(Difference(false), And(doubling, Difference(true)))));
        return Disp(AlphaBinder(Implies(Primitive(), body)));
    }
    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("singertrace-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) => new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula NotMember(Formula a, Formula b) => new Formula.Not(Parenthesized(Member(a, b)));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Equivalent(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(Formula a, Formula type, Formula body) => Seq(Forall, Sp, a, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula PlusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MinusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula TimesOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Prime() => QCall("Nat", "Prime", P());
    private static Formula P() => F.Id("p");
    private static Formula AlphaValue() => Alpha;
    private static Formula Field() => Call("GaloisField", P(), F.D(3));
    private static Formula Scalars() => Call("ZMod", P());
    private static Formula Index() => Call("Fin", PlusOf(PlusOf(Power(P(), F.D(2)), P()), F.D(1)));
    private static Formula BaseBinder(Formula body) => All(P(), Naturals(),
        Seq(OpenBracket, Call("Fact", Prime()), CloseBracket, Comma, Sp, body));
    private static Formula AlphaBinder(Formula body) => BaseBinder(All(AlphaValue(), Field(), body));
    private static Formula Value(Formula i) => Call("val", i);
    private static Formula Trace(Formula x) => QCall("Algebra", "trace", Scalars(), Field(), x);
    private static Formula Filter(Formula i, Formula condition) => QCall("Finset", "filter",
        Seq(Parenthesized(Seq(i, Colon, Sp, Index())), Sp, Mapsto, Sp, condition), QCall("Finset", "univ", Index()));
    private static Formula Count(Formula i, Formula condition) => QCall("Finset", "card", Filter(i, condition));
    private static Formula Primitive() => Equal(Call("orderOf", AlphaValue()), MinusOf(Power(P(), F.D(3)), F.D(1)));
}
