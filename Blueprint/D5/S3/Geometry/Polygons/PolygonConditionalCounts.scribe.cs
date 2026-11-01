using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons.PolygonConditionalCountsFormula;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Polygons;
internal sealed class PolygonConditionalCountsDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string title, Formula statement, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("polygon-conditional-counts-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Geometry/Polygons/PolygonConditionalCounts." + name),
        H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Catalan counts of complete conditioned polygon fibres", H("Actual original chord sets"), Blocks(
        Paragraph(Text("V(n) means ZMod(n); H(n,P) is the subtype of every finite original chord set T satisfying Carrier.IsTriangulation T and P subset EarCenters(T). Triangulation includes internal-diagonal validity, pairwise noncrossing and full maximality. Compatible(P) means that distinct ears with centres in P do not cross. ConditionFiber is the existing complete original-carrier subtype, including its trace constraint; with both trace arguments empty that constraint is automatic. No completion is selected or quotient taken.")),
        Node("forced_card", "All completions containing compatible forced ears", Forced(),
            "The actual iterated deletion equivalence forcedEquiv identifies H(n,P) with every triangulation of the (n-card(P))-gon. The licensed supplier encard_setOf_isTriangulation is applied through the identity on whole chord sets; both carrier inverses are reflexive equalities. Its catalanNumber is definitionally the receiver's Mathlib catalan. This is the containing-event count in B-32, formula (32.1)."),
        Node("Npq", "Integer alternating Catalan sum", Definition(),
            "Npq has values in the integers. All subtractions inside the Catalan index are natural subtraction; choose and catalan are cast to the integers before multiplication. This total definition does not assert any geometric existence or positivity.", DescribeRole.Definition),
        Node("conditional_card", "Every completion with forced P and forbidden Q", Conditional(),
            "For arbitrary disjoint P,Q with compatible union, Mathlib Finset.inclusion_exclusion_card_inf_compl counts the complement of the forbidden-ear events inside the complete forced-P carrier. Every event intersection is equivalent to the complete forced-(P union S) carrier, S subset Q. The term is Catalan(n-card(P)-card(S)-2). Mathlib Finset.sum_powerset_apply_card groups these terms by card(S), giving the binomial coefficient. This proves the cardinality part of (37.3), without its positivity assertion."),
        Paragraph(Text("The source is AURIC_FIB_ATOM_INTRINSIC_CLASSIFICATION_AND_POLYGON_GEOMETRY, B-32 and B-37.2, at revision 4b62d1ff02a702a51332eae3324db7daac400cd5. Its four parameter cases (p,q)=(2,2),(3,3),(2,4),(4,2) are instances of the same theorem at every permitted cyclic placement. Interchanging P,Q is another application with disjointness reversed and union commuted; it uses Nqp, without identifying the weights.")),
        Paragraph(Text("The compatible-card bound gives 2 card(P union Q) <= n. For each j <= card(Q), disjointness gives card(P)+j <= floor(n/2), so n-card(P)-j >= ceil(n/2) >= 7. Thus the displayed Catalan indices are legal ordinary indices; natural truncation in the total definition is inactive on the source domain.")),
        Paragraph(Text("Formula (37.6) follows from this same theorem applied to P union I and Q when I subset E_K(P union Q) and Compatible(I). Membership in E_K supplies disjointness from P union Q and compatibility with every one of its ears. Together with the two internal compatibility assumptions, these facts give compatibility of P union I union Q; card(P union I)=card(P)+card(I). Its ConditionFiber is exactly the original complete carrier with P and I forced and Q forbidden. No new named specialization is retained. Every nonzero term has the same legal-index bound using this larger union.")),
        Paragraph(Text("This delivery does not prove Npq>0, exact-trace formula (37.7), strict flip inequalities, normalized inequality (37.4), or its equality classification. It does not assert a complete formalization of B-37.2. The general structural contraction is the new mathematical construction; Catalan enumeration and generic inclusion-exclusion are reused."))
        ), []));
    private static Formula Forced() => Scope(All("P", Sets, Imp(Lower,
        Imp(C("Compatible", X("P")), Eq(C("Natcard", C("H", X("n"), X("P"))),
            Cat(Sub(Sub(X("n"), Card(X("P"))), N(2))))))));
    private static Formula Definition() => All("n", X("Nat"), All("p", X("Nat"), All("q", X("Nat"),
        Eq(C("Npq", X("n"), X("p"), X("q")),
            SumOver("j", C("range", AddF(X("q"), N(1))),
                Mul(Mul(Pow(Sub(N(0), N(1)), X("j")), AsInt(C("choose", X("q"), X("j")))),
                    AsInt(Cat(Sub(Sub(Sub(X("n"), X("p")), X("j")), N(2))))))))));
    private static Formula Conditional() => Scope(All("P", Sets, All("Q", Sets,
        Imp(Lower, Imp(C("Disjoint", X("P"), X("Q")),
            Imp(C("Compatible", C("union", X("P"), X("Q"))),
                Eq(AsInt(C("Natcard", C("ConditionFiber", X("P"), X("Q"), C("empty"), C("empty")))),
                    C("Npq", X("n"), Card(X("P")), Card(X("Q"))))))))));
}
internal static class PolygonConditionalCountsFormula
{
    internal static Formula X(string n) => F.Id(n);
    internal static Formula N(int n) => n == 14 ? D(1,4) : D((byte)n);
    internal static Formula C(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(X(n))), [.. args]);
    internal static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Operand(Formula f) => f is Formula.Bind ? Seq(Open,f,Close) : f;
    internal static Formula R(Formula a, Formula op, Formula b) => Seq(Open, Operand(a), Sp, op, Sp, Operand(b), Close);
    internal static Formula Eq(Formula a, Formula b) => R(a, F.Eq, b);
    internal static Formula Imp(Formula a, Formula b) => R(a, Implies, b);
    internal static Formula AddF(Formula a, Formula b) => R(a, Plus, b);
    internal static Formula Sub(Formula a, Formula b) => R(a, Minus, b);
    internal static Formula Mul(Formula a, Formula b) => R(a, Cdot, b);
    internal static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    internal static Formula AsInt(Formula a) => Seq(Open,a,Colon,Sp,new Formula.Integers(),Close);
    internal static Formula Cat(Formula a) => C("catalan", a);
    internal static Formula Card(Formula a) => C("card", a);
    internal static Formula Sets => C("Finset", C("ZMod", X("n")));
    internal static Formula Lower => R(N(14), Leq, X("n"));
    internal static Formula Scope(Formula body) => All("n", X("Nat"), Seq(OpenBracket,C("NeZero",X("n")),CloseBracket,Comma,Sp,body));
    internal static Formula SumOver(string v, Formula domain, Formula body) => Seq(Sum,Sp,Underscore,Grp(X(v),InMacro,Sp,domain),Sp,Open,body,Close);
}
