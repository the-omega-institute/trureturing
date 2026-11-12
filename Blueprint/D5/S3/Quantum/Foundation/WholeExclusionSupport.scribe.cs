using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class WholeExclusionSupportDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessOrEqual, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula App(Formula f, Formula x) => Call("apply", f, x);
    private static Formula R => Seq(Mathbb, Grp(V("R")));

    public DocumentDefinition Create()
    {
        Formula space = V("V"), cone = V("C"), unit = V("u"), h = V("h"), r = V("r"), x = V("x");
        Formula dual = Call("LinearMap", R, space, R);
        Formula premise = And(Call("IsClosed", cone), And(
            All("x", space, Imp(And(In(x, cone), Seq(x, Neq, Sp, D(0))),
                Seq(D(0), F.Lt, Sp, App(unit, x)))), And(
            Eq(App(h, r), D(1)), And(
            All("x", space, Imp(In(x, cone), Le(App(h, x), App(unit, x)))),
            All("x", space, Imp(In(x, Call("exclusion", cone, unit, r)), Eq(App(h, x), D(0))))))));
        Formula statement = All("V", V("Type"), Seq(
            Seq(OpenBracket, Call("NormedAddCommGroup", space), CloseBracket),
            Seq(OpenBracket, Call("NormedSpace", R, space), CloseBracket),
            Seq(OpenBracket, Call("FiniteDimensional", R, space), CloseBracket),
            All("C", Call("PointedCone", R, space),
            All("u", dual, All("r", Call("pure", cone, unit), All("h", dual,
                Imp(premise, Call("confirms", cone, unit, r, h))))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Global positivity of a candidate vanishing on the entire original exclusion set.",
            H("Whole original exclusion support"),
            Blocks(
                Paragraph(Text("The carrier is any finite dimensional real normed vector space V, with an original closed pointed cone C and a linear unit u strictly positive on C away from zero. The existing definitions are K=base(C,u)={x in C : u(x)=1}, P=pure(C,u)=ext(K), proper(C,u,f) meaning 0<=f(x)<=u(x) for every x in C, and confirms(C,u,r,f) meaning proper(C,u,f) and f(r)=1. The entire original exclusion set is D_r=exclusion(C,u,r)={x in K : there exists one original proper f with f(r)=1 and f(x)=0}. The quantifier over effects is the full interval, and D_r contains all such mixed states.")),
                Describe.Lean(DescribeId.Create("whole-exclusion-support"),
                    DeclarationHandle.Create("D5/S3/Quantum/Foundation/WholeExclusionSupport.whole_exclusion_support"),
                    H("A whole-exclusion zero condition forces global positivity"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every original pure r and real linear h, assume h(r)=1, h<=u on the entire original cone, and h vanishes on all of D_r. Then h is an original proper confirmer of r. No positivity of h, finite frame, dimension-two condition, face classification, least effect or joint frame is an assumption. Generatingness and nontriviality are unnecessary for this prerequisite; every instance of the original source domain is included.")),
                        Paragraph(Text("Compactness of the entire base gives a minimizing state x and c=h(x). If c<0, construct g=(h-cu)/(1-c). Its lower bound follows from the minimum on every original pure point; its upper bound follows from h<=u. The existing cone_bound theorem then proves that g is proper on every original cone vector. The same g has g(r)=1 and g(x)=0, so x belongs to the entire D_r. The assumed vanishing forces c=0, a contradiction. The minimum is therefore nonnegative, and the existing nonneg_on_cone theorem extends the conclusion to the entire cone. A mixed minimizing state suffices, so no extreme-point selection theorem is needed.")),
                        Paragraph(Text("This is the global normalization prerequisite used in VII 103.5 and VII 104.3, with VII 104.9 as its finite-pure target. For a prospective three-effect frame, substitute h=u-a_p-a_q only after establishing h(r)=1 and a_p+a_q=u on the entire D_r from the original EB and Pair_perp entrance. This theorem does not establish those geometric premises or assert the joint frame. The original finite-ALL-P claim remains: EB_ge1 plus Pair_perp and finiteness of all original ext(K) imply that the entire K is a classical triangle, with all consequences of VII104.16. Unpaid bridges are the EB-to-whole-face geometry, local orthogonal-pair and frame construction, finite-polytope facet existence and dimension control, whole-base barycentric reconstruction, and the full classical effect, face-lattice and same-cone/unit EJA consequences. No smaller conditional theorem is identified with VII104.9. No literature priority is asserted."))),
                    DescribeRole.Theorem))));
    }
}
