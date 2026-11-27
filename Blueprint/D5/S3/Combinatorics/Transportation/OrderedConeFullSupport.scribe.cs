using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Transportation;

internal sealed class OrderedConeFullSupportDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef AK =
        LibraryNoteRef.Create("D5/L/Semigroups/atserias2025witnesses");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order density is equivalent to exact full permitted support in every balanced finite-fiber transportation problem over the original nonnegative cone.",
        H("Density and full permitted support in ordered-group cones"),
        Blocks(Describe.Lean(DescribeId.Create("ordered-cone-density-full-support"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Transportation/OrderedConeFullSupport.density_iff_full_permitted_support"),
            H("The full equivalence"), StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(AK), Blocks(
                Paragraph(Text("There are four independent universes u, v, w and z. G has type Typeu and carries an additive commutative group, a linear order and the compatibility IsOrderedAddMonoid. A has type Typev, B has type Typew, and Z has type Typez. Only A and B are finite. Nonneg(G) is exactly the subtype of x in G satisfying zero less than or equal to x. Its zero, addition, natural repeated addition, finite sums and equality are the original operations restricted to that subtype; no multiplication or division is used.")),
                Paragraph(Text("In the displayed formula, Arrow(U,V) denotes the function type U to V. For arbitrary label maps f and g and nonnegative margins p and q, fiberSum(f,p,c) means the sum over A of p(a) when f(a)=c and zero otherwise, and similarly for B. The expression rowSum(m,a) is the sum over B of m(a,b), and columnSum(m,b) is the sum over A of m(a,b). Balance requires equality of the two fiber sums for every c in Z. A permitted cell has equal labels and two nonzero margins. The conclusion provides one matrix m with exactly the original row and column sums, zero entries off equal labels, and a nonzero entry at every and only permitted cell.")),
                Paragraph(Text("For the forward direction, collect all strictly positive values among the two finite margin families. If this set is nonempty, let d be its minimum and n the sum of the row and column cardinalities. Density gives a positive e with n repeated additions of e strictly below d, by exists_nsmul_lt_of_pos. This uses neither an Archimedean assumption nor divisibility. Put e in every permitted cell and zero in every other cell. Each seed row is at most the column cardinality repeated additions of e, and each seed column is at most the row cardinality repeated additions of e. These bounds fit within their original margins. If there are no positive margins, the zero seed suffices.")),
                Paragraph(Text("Subtract each seed row and column sum in G. The residuals are nonnegative. For every label the two removed totals agree, because off-label seed cells vanish and finite summation commutes. The original cone is conical, and comparing the first two summands constructs binary refinement by subtraction of the smaller first margin. Apply the existing finite_fiber_transport construction to the residual cone-valued margins, then add the seed back. The same matrix has exact original margins and retains every positive seed cell. Conicality forces every entry in a zero row or column to vanish.")),
                Paragraph(Text("For the converse, fix a<b and use the positive cone element x=b-a. Take two rows and two columns, all four margins equal to x and all labels equal. Full permitted support makes both entries in the first row strictly positive; their sum is x. Its first entry t therefore satisfies zero<t<x, so a+t lies strictly between a and b. The row carrier is ULift of Bool at universe v, the column carrier is ULift of Bool at universe w, and the label carrier is ULift of Unit at universe z. Thus this argument uses the original arbitrary carrier universes, rather than restricting the statement to small types.")),
                Paragraph(Text("The statement includes the trivial group, non-Archimedean groups, empty row or column carriers, zero margins, empty fibers, and arbitrary possibly empty label types. The construction sums only over the two finite carriers, never over Z. The result gives existence and exact support, without asserting uniqueness, a uniform lower bound independent of the margins, or an algorithm with a specified running time.")),
                Paragraph(Text("The feasible transportation supplier is the conical binary-refinement construction in FiniteTransport. This ordered-cone equivalence refines that feasibility result to simultaneous full permitted support. It addresses an ordered-group-cone class related to the largest-support question in Atserias and Kolaitis, Section 8; it does not classify all coefficient monoids or settle that broader question."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args) => Call(name, args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula L(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(a, op, b);
    private static Formula And(Formula a, Formula b) => L(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => L(a, FormulaLogicOperator.Implies, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Arr(Formula a, Formula b) => C("Arrow", a, b);
    private static Formula Inst(string name, Formula carrier, Formula body) =>
        Seq(OpenBracket, C(name, carrier), CloseBracket, Comma, Sp, body);
    private static Formula Statement()
    {
        Formula G=V("G"), A=V("A"), B=V("B"), Z=V("Z"), K=C("Nonneg",G);
        Formula a=V("a"), b=V("b"), c=V("c"), f=V("f"), g=V("g"), p=V("p"), q=V("q");
        Formula entry=C("m",a,b), pa=C("p",a), qb=C("q",b);
        Formula labels=Equal(C("f",a),C("g",b));
        Formula balance=All("c",Z,Equal(C("fiberSum",f,p,c),C("fiberSum",g,q,c)));
        Formula off=All("a",A,All("b",B,Imp(Ne(C("f",a),C("g",b)),Equal(entry,D(0)))));
        Formula rows=All("a",A,Equal(C("rowSum",V("m"),a),pa));
        Formula cols=All("b",B,Equal(C("columnSum",V("m"),b),qb));
        Formula support=All("a",A,All("b",B,L(Ne(entry,D(0)),FormulaLogicOperator.Iff,
            And(labels,And(Ne(pa,D(0)),Ne(qb,D(0)))))));
        Formula witness=Ex("m",Arr(A,Arr(B,K)),And(off,And(rows,And(cols,support))));
        Formula transport=All("A",V("Typev"),All("B",V("Typew"),All("Z",V("Typez"),
            Inst("Fintype",A,Inst("Fintype",B,
                All("f",Arr(A,Z),All("g",Arr(B,Z),All("p",Arr(A,K),All("q",Arr(B,K),
                    Imp(balance,witness))))))))));
        return All("G",V("Typeu"),Inst("AddCommGroup",G,Inst("LinearOrder",G,
            Inst("IsOrderedAddMonoid",G,L(C("DenselyOrdered",G),FormulaLogicOperator.Iff,transport)))));
    }
}
