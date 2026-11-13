using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class RegularAnchorContactCriterionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/RegularAnchorContactCriterion.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);

    public DocumentDefinition Create()
    {
        Formula r=Seq(Mathbb,Grp(V("R"))), space=V("V"), cone=V("C"), unit=V("u"),
            p=V("p"), e=V("e"), a=V("a"), n=V("n"), x=V("x");
        Formula dual=C("LinearMap",r,space,r), ball=C("closedBall",D(0),D(1)),
            radius=C("minimum",n), body=C("shell",n), distance=C("boundaryDistance",n);
        Formula contact=C("Nonempty",C("intersection",ball,C("frontier",body)));
        Formula strict=Imp(Seq(D(1),F.Lt,Sp,radius),And(
            C("subset",C("smul",radius,ball),body),And(
                C("subset",ball,C("interior",body)),And(
                    Le(Seq(radius,Minus,D(1)),distance),Seq(D(0),F.Lt,Sp,radius,Minus,D(1))))));
        Formula criterion=And(Iff(Eq(C("width",a),D(1)),Eq(radius,D(1))),
            And(Iff(Eq(radius,D(1)),contact),strict));
        Formula result=Ex("n",C("NativeChart",cone,unit,p,e,a),C("ContactCriterion",n));
        Formula quantified=All("p",C("pure",cone,unit),All("e",dual,
            Imp(C("common",cone,unit,p,e),Imp(C("Regular",cone,unit,p),
                All("a",C("FullBall3Chart",cone,unit,p),result)))));
        Formula hypotheses=Imp(C("IsClosed",cone),Imp(
            All("x",space,Imp(C("mem",x,cone),Imp(Seq(x,Neq,Sp,D(0)),
                Seq(D(0),F.Lt,Sp,C("apply",unit,x))))),Imp(
                    Eq(C("span",r,cone),C("top")),Imp(C("EB3",cone,unit),
                        Imp(C("exclusionInjective",cone,unit),quantified)))));
        Formula statement=All("V",V("Type"),Seq(
            OpenBracket,C("NormedAddCommGroup",space),CloseBracket,Sp,
            OpenBracket,C("NormedSpace",r,space),CloseBracket,Sp,
            OpenBracket,C("FiniteDimensional",r,space),CloseBracket,Sp,
            All("C",C("PointedCone",r,space),All("u",dual,hypotheses))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The original regular-anchor system satisfies the complete width, minimum and actual shell-contact equivalence, with positive strict-scale distance.",
            H("Regular-anchor contact and shell scale"),Blocks(
                Paragraph(Text("This is Theorem 122.13, equation Q122.34. V is the original finite dimensional real normed space. C is the original closed generating convex cone, and u is strictly positive on every nonzero point of C. Strict positivity implies salience: x and -x cannot both be nonzero cone elements, since u(-x)=-u(x). No salience follows merely from the name PointedCone.")),
                Paragraph(Text("The entire original normalized base is K={x in C:u(x)=1}; P consists of all its extreme points. The effect interval E contains every original real-linear f with 0<=f<=u on all C. F_p={f in E:f(p)=1}, T_p(x)=min over F_p of f(x), and D_p={x in K:T_p(x)=0}. The existing comparison-attainment theorem identifies this set with the full exclusion, including its mixed states. A_p consists of all common effects e in F_p that vanish on all D_p. Regular(C,u,p) means A_p is a singleton. The supplied e is its member and therefore is exactly e_p.")),
                Paragraph(Text("EB3 asserts that every original pure label has a chart of its entire exclusion by the closed three-ball. Exclusion injectivity means D_p=D_q implies p=q for all original pure p,q. For the fixed anchor the supplied chart a has an injective affine map with a(closedBall(0,1))=D_p. In source notation c=a(0) and B=a.linear, so D_p=c+B closedBall(0,1). Its linear directions lie in ker(u). There is no assumption that the pure-state set is closed, and no pair, global leastness, matrix representation or dimension reduction premise.")),
                Paragraph(Text("Apply RegularAnchorNormalChart.regular_anchor_native to precisely these hypotheses, p,e and a. It derives the restriction isomorphism on the real span of N_p={h>=0 on C:h(p)=0}, the actual linear H with H(a(w))=w, H(p)=0 and each coordinate in span(N_p), and g=u-e. It proves g>0 on all K except p, g(a(w))=1 for every coordinate w, and a finite positive M with norm(H(x))<=M*g(x) on the whole cone. Thus the normal interface, its support bounds and its actual three-dimensional coordinates are conclusions.")),
                Paragraph(Text("Define Z={H(x)/g(x):x in K except p}, S=closure(Z), rho(v)=sup over Z of -inner(v,z), and delta=min over the entire unit sphere of rho. The same original state supplies both H(x) and g(x). RegularAnchorWidthAntipode.actual_image_bound and ball_subset_actual give boundedness and the entire unit ball in Z. The proved perspective construction gives convexity of Z. The shell is consequently compact and convex with nonempty ambient interior, and its support in direction -v is exactly rho(v).")),
                Paragraph(Text("The definitions width(a), minimum(n), shell(n) and boundaryDistance(n) are the original W(D_p), delta, S and set distance, respectively. Width takes the supremum of the entire original effect interval; width_attained proves that this is a maximum and supplies an actual effect and two antipodal chart states. The directional supremum is finite and Lipschitz. minimum_attained proves that its sphere infimum is a minimum and that delta>=1. boundaryDistance is the real infimum of dist(x,y) over the whole closed unit ball and the whole shell frontier; both sets are nonempty. The formula below uses smul for scalar multiplication of the whole set, intersection for set intersection and subset for set inclusion.")),
                Describe.Lean(DescribeId.Create("contact-criterion"),DeclarationHandle.Create(Owner+"ContactCriterion"),
                    H("All contact and strict-scale clauses"),StatementSource.FromAuthor(Disp(
                        Iff(C("ContactCriterion",n),criterion))),AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("Here n is the derived normal chart for the same C,u,p,e,a. The displayed conjunction means width one if and only if minimum one, minimum one if and only if the closed unit ball meets the boundary of its actual shell, and the complete strict-delta conclusion. By transitivity it includes both directions between every pair of the three contact conditions. All boundaries and interiors are ambient in the actual coordinate space EuclideanSpace(R,Fin(3))."))),DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("original-contact"),DeclarationHandle.Create(Owner+"regular_anchor_contact_criterion"),
                    H("Complete criterion on the original telescope"),StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),Blocks(
                        Paragraph(Text("The notation exclusionInjective(C,u) in the display means injectivity of p -> exclusion(C,u,p) on the entire original pure carrier. NativeChart in the existential conclusion is derived from the original hypotheses; no normal chart, H, support representation, continuity or attained minimum is supplied as an additional premise.")),
                        Paragraph(Text("For width one, width_attained gives a full original effect with oscillation one at a unit direction's antipodal states. The original effect bounds make its endpoint readings exactly one and zero. rho_one_iff_antipodal, using the original comparison and positive normal-body interfaces, gives rho(v)=1. Conversely rho(v)=1 supplies a full original separating effect, hence width one. This is width_one_iff_rho_one on the entire original effect domain. Since the attained sphere minimum is at least one, existence of a unit direction with rho(v)=1 is equivalent to delta=1, in both directions.")),
                        Paragraph(Text("If rho(v)=1 for a unit v, the actual point -v belongs to Z and saturates -inner(v,z)<=1 on S. A neighborhood in S would contain a point farther in direction -v and violate that inequality, so -v is on the boundary. Conversely a contact z in closedBall(0,1) and frontier(S) has a supporting nonzero functional. Its normalized Riesz vector b satisfies 1<=inner(b,z)<=norm(z)<=1. Equality gives norm(z)=1 and b=z, and therefore rho(-z)=1. These are the exact signs of rho_one_frontier and ball_frontier_direction. minimum_one_iff_contact supplies the second displayed equivalence.")),
                        Paragraph(Text("For delta>1, the proved separation theorem mem_shell_iff reconstructs the actual closed convex S from all its unit support halfspaces. Cauchy-Schwarz and delta<=rho(v) put every vector of norm at most delta in S, by minimum_ball_subset. Because delta is positive, the standard smul_unitClosedBall identity identifies this closed ball with delta times the entire closed unit ball. strict_margin puts the original unit ball in interior(S). Every frontier point has norm at least delta; the triangle inequality gives dist(x,y)>=delta-1 for every original inner-ball x and every frontier y. strict_boundary_distance takes the nonempty distance-value infimum and proves boundaryDistance>=delta-1>0.")),
                        Paragraph(Text("This is a conditional mathematical statement on the declared original cone and effect system. It neither assumes smoothness, strict convexity or closedness of Z nor derives contact from those properties. It makes no physical realization or literature novelty claim."))),DescribeRole.Theorem)
            )));
    }
}
