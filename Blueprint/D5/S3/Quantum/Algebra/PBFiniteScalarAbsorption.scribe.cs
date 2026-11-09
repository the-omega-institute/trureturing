using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBFiniteScalarAbsorptionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite matrix evaluations of the original total response absorb semidefinite second images and force Jordan orthogonality for every second image.",
        H("Scalar first images and semidefinite actual second images"),
        Blocks(Describe.Lean(DescribeId.Create("semidefinite-second-image"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBFiniteScalarAbsorption.semidefinite_second_image"),
            H("Semidefinite second-image absorption"),
            StatementSource.FromAuthor(Disp(Statement(false))), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("O is the existing OriginalData on the same real normed label space E, with its faithful isometric JC carrier i into a complex C-star algebra A, unit u, bilinear Jordan product J, arbitrary total response D, original preparations, exact detected cone and every original directed positive two-table. q maps E real-linearly into the full selfadjoint complex matrix space on a finite index type n. It preserves the unit and Jordan product and sends the original cone to positive semidefinite matrices. q need not be injective. All finite dimensions are included, including the empty matrix index type; no restriction to a corner, traceless inputs or a response on the image is made.")),
                Paragraph(Text("The displayed implication holds when q(a)=mu I and q(b) or -q(b) is positive semidefinite. mu can be positive, negative or zero, and b can have zero image. Density, surjectivity, roots, positive lifts and completeness of E are not assumptions of this first bridge. The full scalar-first-image theorem for arbitrary second images, its continuous-bundle realization and original65.2 remain outside this statement.")),
                Paragraph(Text("For any vector, the cone-positive mathematical vector functional composed with q reads the same original P2 by positive_table_transfer. These readings include zero vectors and arbitrary masses; they add no actual preparations. Matrix action, restricted to the real inner product on the same complex Euclidean space, gives the existing Readout on all original labels. In particular P2 forces the evaluated response on every actual proportional pair (a,k a) to vanish.")),
                Paragraph(Text("Write H=D(a,b), h=q(H), B=q(b). If h is nonzero, a Hermitian eigenvector w has h w=Z w with Z nonzero and w nonzero. Put k=Z/(1+mu squared), c=k a, nu=H-J(a,c), omega=J(a,b)+D(a,c). These are actual original labels. PB uses D(b+nu,c+omega) and D(b-nu,c-omega), without deleting D(a,c) from either label. Only its matrix image is zero. On w the two second labels equal respectively mu and -mu times the first labels. Both real Gram determinants and hence both outer response readings vanish.")),
                Paragraph(Text("Reading the literal PB right side then gives Z times the expectation of B equal to zero. Since Z is nonzero and B or -B is positive semidefinite, the matrix positive-semidefinite null-quadratic criterion gives B w=0. The original P2 for (a,b) now has zero second diagonal and forces Z times the squared norm of w to vanish, contradicting both nonzero conditions. This eigenvector/PB argument is the new load-bearing inference; existing spectral decomposition and positivity-transfer facts are applied directly.")),
                Paragraph(Text("This proves the semidefinite-image step of fixed OP4.2, equations (4.5)-(4.7), for full finite matrix targets. The next theorem supplies the semidefinite rank-one correction from genuine original squares and the PB readings for every vector. The second fixed table, spectral relation and final fourth-power argument remain outside the two statements. No regularity, homogeneity, additivity, quotient descent or replacement response is assumed."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("scalar-second-jordan-zero"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBFiniteScalarAbsorption.scalar_second_jordan_zero"),
            H("Jordan orthogonality of every second image"),
            StatementSource.FromAuthor(Disp(Statement(true))), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Retain exactly the same original data and evaluation, and suppose the real-linear range q(E) is dense in the full finite selfadjoint matrix space, with its Euclidean operator norm. This range is a finite-dimensional real subspace, hence closed, so density makes q surjective. For every positive semidefinite matrix M, choose an original e whose image is the positive matrix square root of M. Jordan compatibility gives q(J(e,e))=M. A negative semidefinite image is lifted by -J(e,e). Thus the correction labels below are actual original signed squares, rather than newly postulated positive representatives.")),
                Paragraph(Text("Fix a,b with q(a)=mu I and write H=D(a,b), h=q(H), B=q(b). The conclusion is q(J(b,H))=0, equivalently Bh+hB=0. This does not yet say h=0. If mu=0, the original P2 has zero first diagonal and already makes h=0. If h=0, the Jordan conclusion follows directly. These branches include the zero target and all zero vectors.")),
                Paragraph(Text("For a vector v with nonzero real expectation of h, put tau=mu/(1+mu squared), W=tau h v and r=inner(v,W). In the remaining branch mu is nonzero, so r is nonzero. Let M be the positive rank-one matrix represented by the operator z maps to inner(W,z) W, and let C=M/r. According to the sign of r, C or -C is positive semidefinite. The original square lifts give c with q(c)=C, and the preceding absorption theorem gives q(D(a,c))=0. Selfadjointness gives inner(W,v)=r, so C v=W and (1+mu squared) C v=mu h v.")),
                Paragraph(Text("Use the literal PB labels nu=H-J(a,c), omega=J(a,b)+D(a,c). On this same v, the two outer second-label vectors are respectively mu and -mu times their first-label vectors. P2 therefore makes both outer output expectations zero. The exact PB right side reduces to inner(Bv,hv)=0, which is the expectation of q(J(b,H)). No response image has been assumed to vanish except the already proved semidefinite case.")),
                Paragraph(Text("Vectors with zero expectation of h are included by an algebraic argument on fixed readings. If h is nonzero, choose w with nonzero expectation of h. For any v, the functions f(t)=inner(v+t w,h(v+t w)) and g(t)=inner(v+t w,q(J(b,H))(v+t w)) are real quadratic polynomials. The leading coefficient of f is nonzero. The nonzero-expectation argument gives f(t)g(t)=0 for every real t, so polynomial extensionality and the integral-domain law give g=0. Its constant coefficient is the required reading at v. Symmetric-operator polarization then gives q(J(b,H))=0. This is a polynomial identity for two fixed known matrices; no limit, continuity or regularity of the unknown original response enters.")),
                Paragraph(Text("The next unpaid finite-matrix steps are the second fixed original table with images X=mu(I-B squared)-h, Y=2mu B and response 2mu h, its spectral implication (B squared-I)h=0, and the final actual PB call (y,x,0) read through positive h-sandwich functionals to obtain h to the fourth power zero. The full continuous-bundle evaluation and original65.2 are separate remaining obligations."))),
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
    private static Formula Statement(bool orthogonal)
    {
        var A=I("A"); var E=I("E"); var P=I("P"); var n=I("n"); var O=I("O");
        var q=I("q"); var a=I("a"); var b=I("b"); var mu=I("mu");
        var real=Seq(Mathbb,Grp(I("R"))); var complex=Seq(Mathbb,Grp(I("C")));
        var M=C("Matrix",n,n,complex);
        Formula Q(Formula x) => C("coerce",C("apply",q,x));
        Formula J(Formula x, Formula y) => C("apply",C("Jordan",O),x,y);
        Formula D(Formula x, Formula y) => C("apply",C("response",O),x,y);
        var jordanProduct=C("smul",new Formula.Fraction(N(1),N(2)),
            C("add",C("mul",Q(I("x")),Q(I("y"))),C("mul",Q(I("y")),Q(I("x")))));
        var jordan=All("x",E,All("y",E,Eq(Q(J(I("x"),I("y"))),jordanProduct)));
        var positive=All("x",E,Imp(Le(N(0),C("apply",C("embedding",O),I("x"))),C("PosSemidef",Q(I("x")))));
        var assumptions=And(Eq(Q(C("unit",O)),C("one",M)),And(jordan,And(positive,C("PB",C("Jordan",O),C("response",O)))));
        var condition=And(Eq(Q(a),C("smul",mu,C("one",M))),Or(C("PosSemidef",Q(b)),C("PosSemidef",C("negate",Q(b)))));
        var conclusion=All("a",E,All("b",E,All("mu",real,Imp(condition,Eq(C("apply",q,D(a,b)),N(0))))));
        if (orthogonal)
        {
            assumptions=And(assumptions,C("DenseRange",q));
            conclusion=All("a",E,All("b",E,All("mu",real,
                Imp(Eq(Q(a),C("smul",mu,C("one",M))),Eq(C("apply",q,J(b,D(a,b))),N(0))))));
        }
        var body=All("O",C("OriginalData",A,E,P),All("q",C("LinearMap",real,E,C("selfAdjoint",M)),Imp(assumptions,conclusion)));
        return All("A",I("Type"),All("E",I("Type"),All("P",I("Type"),All("n",I("Type"),Seq(
            OpenBracket,C("CStarAlgebra",A),CloseBracket,OpenBracket,C("PartialOrder",A),CloseBracket,
            OpenBracket,C("NormedAddCommGroup",E),CloseBracket,
            OpenBracket,C("NormedSpace",real,E),CloseBracket,OpenBracket,C("Fintype",n),CloseBracket,
            OpenBracket,C("DecidableEq",n),CloseBracket,body)))));
    }
}
