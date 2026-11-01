using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGeometry;

internal sealed class ProjectivePlaneRealSectorsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGeometry/ProjectivePlaneRealSectors.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete real incidence sectors and the exact centered-Gram positivity interval of each actual finite projective plane.",
        H("Original-incidence real sectors and centered distances"), Blocks(
            Paragraph(Text("Let P and L be the original finite point and line types, with their original membership and a nondegenerate Configuration.ProjectivePlane instance. Put q=order(P,L), v=q^2+q+1 and s=sqrt(q). The existing integer incidence totals and intersection identities give N*N^T=qI+J and N^T*N=qI+J after casting to the reals. They also give N1=(q+1)1 and N^T1=(q+1)1. The order satisfies q>=2; no plane is asserted to exist at an arbitrary prescribed integer q.")),
            Def("orderR", "Real order", "The integer order of the original plane, cast to the reals."),
            Def("incidenceMatrix", "Original incidence matrix", "N has original point rows and original line columns, with N(p,l)=1 precisely when p belongs to l."),
            Def("toPoints", "Real incidence", "The linear map y mapped to N*y on original line coordinates."),
            Def("toLines", "Transposed real incidence", "The linear map x mapped to N^T*x on original point coordinates."),
            Def("zeroSum", "Zero-sum coordinates", "zeroSum(I) is the submodule of real I-coordinate vectors whose full coordinate sum is zero, including the empty index type."),
            Def("rootOrder", "Positive incidence singular value", "s=sqrt(q)>0 for the actual plane."),
            Def("normalizedToLines", "Normalized transposed incidence", "On original point zero-sum coordinates, x is mapped to N^T*x/s."),
            Def("normalizedToPoints", "Normalized incidence", "On original line zero-sum coordinates, y is mapped to N*y/s."),
            Def("balancedEquiv", "Equivalence of the balanced coordinate spaces", "The two normalized maps are mutually inverse. Their compositions reduce to q/s^2 times the identity because the all-ones terms vanish on zero-sum vectors."),
            Def("mean", "Finite coordinate mean", "mean(x)=card(I)^(-1)*sum_i x(i), with real inverse-zero convention."),
            Def("splitConstant", "Constant and zero-sum splitting", "For a finite I with nonzero cardinality, x is identified with its mean and x minus that constant mean. The inverse adds the constant coordinate back."),
            Def("sectorEquiv", "Four-sector coordinate equivalence", "S sends ((c,b),(x,y)) to (c+b+x+y, c-b+T(x-y)), where x,y belong to zeroSum(P) and T=N^T/s. This is a linear equivalence onto all original point/line coordinate pairs, with no assumed diagonalization."),
            Def("sectorConstant", "Constant line", "The c coordinate alone gives (c*1,c*1)."),
            Def("sectorBipartition", "Bipartition line", "The b coordinate alone gives (b*1,-b*1)."),
            Def("sectorPlus", "Positive nonconstant sector", "The x coordinate alone gives (x,T*x), for all original point zero-sum vectors x."),
            Def("sectorMinus", "Negative nonconstant sector", "The y coordinate alone gives (y,-T*y), for all original point zero-sum vectors y."),
            Thm("existsUnique_sector_coordinates", "Complete unique sector coordinates", UniqueFormula(),
                "Every original coordinate pair has exactly one four-sector coordinate vector. The normalized incidence equivalence supplies the inverse on the line zero-sum part; the means supply the two constant coordinates."),
            Thm("sector_finranks", "Exact dimensions of the four sectors", DimensionsFormula(),
                "The dimensions of the constant, bipartition, positive and negative sectors are respectively 1, 1, v-1 and v-1. The maps into these sectors are injective. Constant/zero-sum splitting has total dimension v, so its zero-sum factor has dimension v-1."),
            Def("vertexDot", "Original Euclidean coordinate form", "The dot product is the point-coordinate dot product plus the line-coordinate dot product."),
            Thm("sectorEquiv_dot", "Orthogonal sector formula", DotFormula(),
                "For z=((c,b),(x,y)) and w=((d,e),(u,t)), the dot product of S(z) and S(w) is 2v*(c*d+b*e)+2*(dot(x,u)+dot(y,t)). Thus all four sectors are mutually orthogonal. The normalized incidence equivalence preserves the zero-sum dot product."),
            Def("adjacency", "Original incidence adjacency", "A sends (x,y) to (N*y,N^T*x). Its labels and membership come from the actual plane."),
            Def("center", "Uniform vertex centering", "H subtracts the average of the point mean and the line mean from both coordinate vectors. The side cardinalities coincide, so this is centering over all 2v original vertices."),
            Def("gramAction", "Centered two-distance Gram operator", "For every real delta, B=delta*H/2+(delta-1)*H*A*H/2."),
            Def("bipartitionScalar", "Bipartition scalar", "beta(delta)=(q+1-q*delta)/2."),
            Def("plusScalar", "Positive-sector scalar", "alpha(delta)=((1+s)*delta-s)/2."),
            Def("minusScalar", "Negative-sector scalar", "gamma(delta)=(s+(1-s)*delta)/2."),
            Thm("gramAction_sector", "Complete centered-Gram scalar action", ActionFormula(),
                "The four scalar actions of B are 0, beta(delta), alpha(delta), gamma(delta), respectively. This equality holds for every real delta, including every singular value of the parameter."),
            Thm("gramAction_nonnegative_iff", "Positivity tests every nonconstant sector", ScalarCriterionFormula(),
                "The Gram form is nonnegative on every original coordinate pair exactly when beta, alpha and gamma are all nonnegative. Necessity uses the actual bipartition direction and actual nonzero point zero-sum vectors. Sufficiency uses the complete orthogonal formula, with all coordinate squares nonnegative."),
            Thm("gramAction_nonnegative_interval", "Exact positivity interval", IntervalFormula(false),
                "Nonnegativity holds exactly for s/(1+s)<=delta<=(q+1)/q. The lower endpoint comes from the positive incidence sector and the upper endpoint from the bipartition sector. The negative incidence scalar is nonnegative throughout this interval."),
            Def("vertexEquiv", "Original disjoint vertex coordinates", "A real function on P+L is identified with its restrictions to the original points and original lines."),
            Def("adjacencyMatrix", "Original block adjacency matrix", "The matrix has blocks (0,N;N^T,0)."),
            Def("distanceMatrix", "Original squared two-distance assignment", "D=delta*(J-I)+(1-delta)*A. Its diagonal is zero; original incident point-line pairs have squared distance value one, and every other distinct pair has value delta."),
            Def("centeringMatrix", "The actual centering matrix", "H=I-card(P+L)^(-1)*J on all original vertices."),
            Def("centeredGram", "Doubly centered distance matrix", "B=-H*D*H/2. No positive-semidefinite or rank assumption enters this definition."),
            Thm("centeredGram_action", "Matrix and coordinate actions agree", MatrixActionFormula(),
                "Under the original coordinate identification, the actual doubly centered matrix acts exactly as gramAction. The all-ones term is killed by centering, and H is idempotent."),
            Thm("centeredGram_posSemidef_iff", "Exact PSD interval for the original matrix", IntervalFormula(true),
                "The real matrix -H*D*H/2 is positive semidefinite exactly on the stated closed interval. This result concerns the centered matrix. Exact Euclidean realization, sharp matrix rank and minimum ambient dimension require the corresponding reconstruction and rank statements; no plane existence or finite-field embedding into the reals follows from this criterion."),
            Paragraph(Text("This is the classical real symmetric-design incidence decomposition applied to the original projective-plane labels. It does not assume the spectrum as input. Equal coordinate values and singular scalar actions remain in scope. General Euclidean distance reconstruction is the Schoenberg theory discussed in Dokmanic, Parhizkar, Ranieri and Vetterli, Euclidean Distance Matrices: Essential Theory, Algorithms and Applications, section II; the present incidence calculation supplies its specific matrix-positivity condition."))
        ), []));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("real-plane-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Thm(string name, string title, Formula f, string prose) => Describe.Lean(
        DescribeId.Create("real-plane-" + name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(Plane(f))), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Named(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] args) => new Formula.Apply(Named(s), [.. args]);
    private static Formula R() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula P() => F.Id("P");
    private static Formula L() => F.Id("L");
    private static Formula Q() => Call("orderR", P(), L());
    private static Formula S() => Call("rootOrder", P(), L());
    private static Formula V() => Mul(Arrow(P(), R()), Arrow(L(), R()));
    private static Formula C() => Mul(Mul(R(), R()), Mul(Call("zeroSum", P()), Call("zeroSum", P())));
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, To, Sp, b, Close);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula All(Formula x, Formula t, Formula b) => Seq(Forall, Sp, x, Colon, Sp, t, Comma, Sp, b);
    private static Formula Plane(Formula b) => All(P(), Named("Type"), All(L(), Named("Type"), Seq(
        OpenBracket, Call("Membership", P(), L()), CloseBracket, Comma, Sp,
        OpenBracket, Call("Fintype", P()), CloseBracket, Comma, Sp,
        OpenBracket, Call("Fintype", L()), CloseBracket, Comma, Sp,
        OpenBracket, Call("ProjectivePlane", P(), L()), CloseBracket, Comma, Sp, b)));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Fst(Formula z) => Call("fst", z);
    private static Formula Snd(Formula z) => Call("snd", z);
    private static Formula Cc(Formula z) => Fst(Fst(z));
    private static Formula Bb(Formula z) => Snd(Fst(z));
    private static Formula X(Formula z) => Fst(Snd(z));
    private static Formula Y(Formula z) => Snd(Snd(z));
    private static Formula Sector(Formula z) => Call("sectorEquiv", P(), L(), z);
    private static Formula Act(Formula d, Formula z) => Call("gramAction", P(), L(), d, z);
    private static Formula Dot(Formula z, Formula w) => Call("vertexDot", P(), L(), z, w);
    private static Formula Scalar(string name, Formula d) => Call(name, P(), L(), d);
    private static Formula Nn(Formula d) { Formula z=F.Id("z"); return All(z,V(),Le(F.D(0),Dot(z,Act(d,z)))); }
    private static Formula Interval(Formula d) => And(Le(Div(S(),Add(F.D(1),S())),d),Le(d,Div(Add(Q(),F.D(1)),Q())));
    private static Formula UniqueFormula() { Formula z=F.Id("z"), c=F.Id("c"); return All(z,V(),Seq(Exists,Bang,Sp,c,Colon,Sp,C(),Comma,Sp,Eq(Sector(c),z))); }
    private static Formula DimensionsFormula()
    {
        Formula Rank(string n) => Call("finrank",R(),Call("range",Call(n,P(),L())));
        Formula vm=Sub(Call("card",P()),F.D(1));
        return And(Eq(Rank("sectorConstant"),F.D(1)),And(Eq(Rank("sectorBipartition"),F.D(1)),And(Eq(Rank("sectorPlus"),vm),Eq(Rank("sectorMinus"),vm))));
    }
    private static Formula DotFormula()
    {
        Formula z=F.Id("z"),w=F.Id("w");
        Formula right=Add(Mul(Mul(F.D(2),Call("card",P())),Add(Mul(Cc(z),Cc(w)),Mul(Bb(z),Bb(w)))),Mul(F.D(2),Add(Call("dotProduct",X(z),X(w)),Call("dotProduct",Y(z),Y(w)))));
        return All(z,C(),All(w,C(),Eq(Dot(Sector(z),Sector(w)),right)));
    }
    private static Formula ActionFormula()
    {
        Formula d=F.Id("d"),z=F.Id("z");
        Formula right=Pair(Pair(F.D(0),Mul(Scalar("bipartitionScalar",d),Bb(z))),Pair(Mul(Scalar("plusScalar",d),X(z)),Mul(Scalar("minusScalar",d),Y(z))));
        return All(d,R(),All(z,C(),Eq(Act(d,Sector(z)),Sector(right))));
    }
    private static Formula ScalarCriterionFormula() { Formula d=F.Id("d"); return All(d,R(),IffOf(Nn(d),And(Le(F.D(0),Scalar("bipartitionScalar",d)),And(Le(F.D(0),Scalar("plusScalar",d)),Le(F.D(0),Scalar("minusScalar",d)))))); }
    private static Formula IntervalFormula(bool matrix) { Formula d=F.Id("d"); return All(d,R(),IffOf(matrix ? Call("PosSemidef",Call("centeredGram",P(),L(),d)) : Nn(d),Interval(d))); }
    private static Formula MatrixActionFormula()
    {
        Formula d=F.Id("d"),f=F.Id("f");
        return All(d,R(),All(f,Arrow(Call("Sum",P(),L()),R()),Eq(Call("vertexEquiv",P(),L(),Call("mulVec",Call("centeredGram",P(),L(),d),f)),Act(d,Call("vertexEquiv",P(),L(),f)))));
    }
}
