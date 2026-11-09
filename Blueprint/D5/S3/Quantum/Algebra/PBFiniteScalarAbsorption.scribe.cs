using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBFiniteScalarAbsorptionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite matrix evaluation of the original total response absorbs scalar first images against semidefinite second images.",
        H("Scalar first images and semidefinite actual second images"),
        Blocks(Describe.Lean(DescribeId.Create("semidefinite-second-image"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBFiniteScalarAbsorption.semidefinite_second_image"),
            H("Semidefinite second-image absorption"),
            StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("O is the existing OriginalData on the same real normed label space E, with its faithful isometric JC carrier i into a complex C-star algebra A, unit u, bilinear Jordan product J, arbitrary total response D, original preparations, exact detected cone and every original directed positive two-table. q maps E real-linearly into the full selfadjoint complex matrix space on a finite index type n. It preserves the unit and Jordan product and sends the original cone to positive semidefinite matrices. q need not be injective. All finite dimensions are included, including the empty matrix index type; no restriction to a corner, traceless inputs or a response on the image is made.")),
                Paragraph(Text("The displayed implication holds when q(a)=mu I and q(b) or -q(b) is positive semidefinite. mu can be positive, negative or zero, and b can have zero image. Density, surjectivity, roots, positive lifts and completeness of E are not assumptions of this first bridge. The full scalar-first-image theorem for arbitrary second images, its continuous-bundle realization and original65.2 remain outside this statement.")),
                Paragraph(Text("For any vector, the cone-positive mathematical vector functional composed with q reads the same original P2 by positive_table_transfer. These readings include zero vectors and arbitrary masses; they add no actual preparations. Matrix action, restricted to the real inner product on the same complex Euclidean space, gives the existing Readout on all original labels. In particular P2 forces the evaluated response on every actual proportional pair (a,k a) to vanish.")),
                Paragraph(Text("Write H=D(a,b), h=q(H), B=q(b). If h is nonzero, a Hermitian eigenvector w has h w=Z w with Z nonzero and w nonzero. Put k=Z/(1+mu squared), c=k a, nu=H-J(a,c), omega=J(a,b)+D(a,c). These are actual original labels. PB uses D(b+nu,c+omega) and D(b-nu,c-omega), without deleting D(a,c) from either label. Only its matrix image is zero. On w the two second labels equal respectively mu and -mu times the first labels. Both real Gram determinants and hence both outer response readings vanish.")),
                Paragraph(Text("Reading the literal PB right side then gives Z times the expectation of B equal to zero. Since Z is nonzero and B or -B is positive semidefinite, the matrix positive-semidefinite null-quadratic criterion gives B w=0. The original P2 for (a,b) now has zero second diagonal and forces Z times the squared norm of w to vanish, contradicting both nonzero conditions. This eigenvector/PB argument is the new load-bearing inference; existing spectral decomposition and positivity-transfer facts are applied directly.")),
                Paragraph(Text("This proves the semidefinite-image step of fixed OP4.2, equations (4.5)-(4.7), for full finite matrix targets. The next general-second-image step still needs the semidefinite rank-one correction obtained from actual original representatives and its PB readings for every vector, including vectors with zero expectation of h. The later anticommutation, second fixed table, spectral relation and final fourth-power argument are not consequences claimed by this theorem. No regularity, homogeneity, additivity, quotient descent or replacement response is assumed."))),
            DescribeRole.Theorem))));

    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => global::StrataLint.Scribe.DefinitionDsl.Call(s, a);
    private static Formula N(int n) => global::StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Equal(a,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Or,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Statement()
    {
        var A=I("A"); var E=I("E"); var P=I("P"); var n=I("n"); var O=I("O");
        var q=I("q"); var a=I("a"); var b=I("b"); var mu=I("mu");
        var real=Seq(Mathbb,Grp(I("R"))); var complex=Seq(Mathbb,Grp(I("C")));
        var M=C("Matrix",n,n,complex);
        Formula Q(Formula x) => C("coerce",C("apply",q,x));
        Formula J(Formula x, Formula y) => C("apply",C("Jordan",O),x,y);
        Formula D(Formula x, Formula y) => C("apply",C("response",O),x,y);
        var jordan=All("x",E,All("y",E,Eq(Q(J(I("x"),I("y"))),
            C("smul",new Formula.Fraction(N(1),N(2)),C("add",C("mul",Q(I("x")),Q(I("y"))),C("mul",Q(I("y")),Q(I("x")))))));
        var positive=All("x",E,Imp(Le(N(0),C("apply",C("embedding",O),I("x"))),C("PosSemidef",Q(I("x")))));
        var assumptions=And(Eq(Q(C("unit",O)),C("one",M)),And(jordan,And(positive,C("PB",C("Jordan",O),C("response",O)))));
        var condition=And(Eq(Q(a),C("smul",mu,C("one",M))),Or(C("PosSemidef",Q(b)),C("PosSemidef",C("negate",Q(b)))));
        var conclusion=All("a",E,All("b",E,All("mu",real,Imp(condition,Eq(C("apply",q,D(a,b)),N(0))))));
        var body=All("O",C("OriginalData",A,E,P),All("q",C("LinearMap",real,E,C("selfAdjoint",M)),Imp(assumptions,conclusion)));
        return All("A",I("Type"),All("E",I("Type"),All("P",I("Type"),All("n",I("Type"),Seq(
            OpenBracket,C("CStarAlgebra",A),CloseBracket,OpenBracket,C("PartialOrder",A),CloseBracket,
            OpenBracket,C("StarOrderedRing",A),CloseBracket,OpenBracket,C("NormedAddCommGroup",E),CloseBracket,
            OpenBracket,C("NormedSpace",real,E),CloseBracket,OpenBracket,C("Fintype",n),CloseBracket,
            OpenBracket,C("DecidableEq",n),CloseBracket,body)))));
    }
}
