using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBFiniteScalarAbsorptionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dense finite matrix evaluations of the same original total response annihilate every scalar first-image response.",
        H("Scalar-image rigidity in full finite matrix evaluations"),
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
                Paragraph(Text("This proves the semidefinite-image step of fixed OP4.2, equations (4.5)-(4.7), for full finite matrix targets. The next theorem supplies the semidefinite rank-one correction from genuine original squares and the PB readings for every vector. The subsequent statements give the second fixed table, spectral relation and final fourth-power argument. No regularity, homogeneity, additivity, quotient descent or replacement response is assumed."))),
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
                Paragraph(Text("The following theorems use this anticommutation relation in the second fixed table, the spectral constraint and the final actual PB call. The full continuous-bundle evaluation and original65.2 require separate realization arguments."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("scalar-second-actual-table"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBFiniteScalarAbsorption.scalar_second_actual_table"),
            H("The second actual original table"),
            StatementSource.FromAuthor(Disp(Statement(false, 1))), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Use the same O, q, unit, Jordan and cone compatibility, original PB, a, b and real mu, with q(a)=mu I. Density is not needed for this table identity. Write H=D(a,b), B=q(b), h=q(H). In the literal PB call (b,a,mu b), keep nu=D(b,a)-J(b,mu b) and omega=J(b,a)+D(b,mu b). The actual second table has labels x=a+nu and y=mu b+omega. The displayed formula expands these labels, so every occurrence of D remains an original application.")),
                Paragraph(Text("Hermitian symmetry of the original directed tables, transferred to every positive mathematical vector reading, gives q(D(b,a))=-h. Zero real Gram determinants give q(D(b,mu b))=0. Jordan compatibility gives q(J(b,a))=mu B and q(J(b,mu b))=mu B squared. Thus q(x)=mu(I-B squared)-h and q(y)=2mu B. The other actual second label mu b-omega has zero image. Original P2 consequently gives q(D(a-nu,mu b-omega))=0. This is zero-image absorption, and does not identify that actual label with zero.")),
                Paragraph(Text("The literal PB right side has image 2mu h+2mu squared B squared-2mu squared B squared=2mu h. It follows that the actual response q(D(x,y)) is 2mu h. This calculation preserves the inner unknown D terms in both actual outer calls. It never substitutes image-normalized labels into D or uses additivity, homogeneity or continuity of D. The table is used in both the spectral theorem and the final scalar-image theorem."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("scalar-image-spectral"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBFiniteScalarAbsorption.scalar_image_spectral"),
            H("Spectral confinement of the same response"),
            StatementSource.FromAuthor(Disp(Statement(false, 2))), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Retain the full original telescope and assume DenseRange q. Put B=q(b), h=q(D(a,b)). The Jordan orthogonality theorem gives Bh=-hB. Consequently B squared commutes with h. Apply the existing joint-eigenspace decomposition for two commuting symmetric operators to their real actions on the same finite complex Euclidean space. This covers the empty index type and repeated eigenvalues without selecting a nonempty basis.")),
                Paragraph(Text("On a common eigenspace, let B squared v=t v and h v=z v. Zero vectors and z=0 already satisfy (t-1)z=0. Otherwise normalize v. Symmetry and anticommutation give inner(v,Bv)=0 and the squared norm of Bv equal to t. The first actual P2 table gives z squared at most mu squared t, so t is positive and mu is nonzero. With r=sqrt(t) and w=Bv/r, the vectors v,w are orthonormal and Bv=r w, Bw=r v, hv=z v, hw=-z w.")),
                Paragraph(Text("Read the second actual P2 table at c v+s w. Its real Gram determinant is the square of the oriented area of its two action vectors. After cancelling the nonzero factor (2mu) squared, it gives [z(c squared-s squared)] squared at most t[mu(1-t)(c squared-s squared)-z(c squared+s squared)] squared. For each eta between -1 and 1 take c=sqrt((1+eta)/2), s=sqrt((1-eta)/2). Thus (z eta) squared is at most t[mu(1-t)eta-z] squared for every such eta.")),
                Paragraph(Text("The scalar argument includes both signs of mu and z by changing eta to -eta. For positive m=abs(mu), z=abs(z), suppose t differs from 1 and put C=m abs(1-t), which is positive. If z is at most C, eta=z/C makes the right side zero and the left side positive. Otherwise the endpoint with the appropriate sign gives z at most sqrt(t)(z-C), while the first table gives z at most m sqrt(t). These imply sqrt(t)>1 and C at most m(sqrt(t)-1). Substituting C=m(t-1) yields t at most sqrt(t), contradicting sqrt(t)>1. Hence (t-1)z=0. The joint eigenspaces exhaust the whole space, so (B squared-I)h=0."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("scalar-image-zero"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBFiniteScalarAbsorption.scalar_image_zero"),
            H("Full finite-matrix scalar-image absorption"),
            StatementSource.FromAuthor(Disp(Statement(false, 3))), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every original a,b and every real mu with q(a)=mu I, the same actual response has q(D(a,b))=0. All hypotheses are those of OriginalData, real-linear unital Jordan q, positivity on the original cone, literal PB and DenseRange q. The domain E may be incomplete, q may have a kernel, and the finite matrix index type may be empty. No linearity, input regularity, locality, quotient descent or replacement response is imposed on D. The mu=0 branch follows directly from zero-image P2 and image antisymmetry.")),
                Paragraph(Text("For nonzero mu use the actual x,y of the second table. Put d=D(y,x), g=J(y,x). Transferred directed-table symmetry gives q(d)=-2mu h. Direct Jordan multiplication of the two known images, using Bh+hB=0, gives G=q(g)=2mu squared(B-B cubed). The spectral theorem gives B squared h=h, hence Gh=0. Also Xh=-h squared for X=q(x). These identities are calculated from the actual original labels.")),
                Paragraph(Text("Call literal PB(y,x,0). Its original inner labels are nu=d-J(y,0) and omega=g+D(y,0). Bilinearity gives J(y,0)=0, and original P2 gives only q(D(y,0))=0. In particular omega is retained in both unknown outer calls D(x+nu,0+omega) and D(x-nu,0-omega); it is not replaced by g as an argument of D. Their second input images annihilate h, since G h=0.")),
                Paragraph(Text("For each vector v read this equality at h v. This is the positive mathematical h-sandwich functional T maps to inner(hv,T hv), composed with q. Each outer P2 has zero second action vector, so both unknown outer response readings vanish. The exact PB right side reads -4mu times the squared norm of h squared v. Since mu is nonzero, every quadratic reading of h to the fourth power is zero. Symmetric-operator polarization gives h to the fourth power equal to zero. Symmetry then gives h squared v=0 and h v=0 for every v. No limit of unknown outputs or assumption about their dependence on images is used.")),
                Paragraph(Text("This is the finite full-matrix scalar-image implication. Applying it to a continuous matrix bundle still requires construction of the full original data, evaluation/Jordan/cone compatibility and dense evaluation range on that domain. The original65.2 central zero rows and phase conclusion are not asserted by this theorem."))),
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
    private static Formula Statement(bool orthogonal, int completion = 0)
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
        if (completion > 0)
        {
            var scalar=Eq(Q(a),C("smul",mu,C("one",M)));
            Formula result=Eq(C("apply",q,D(a,b)),N(0));
            if (completion == 1)
            {
                var nu=C("subtract",D(b,a),J(b,C("smul",mu,b)));
                var omega=C("add",J(b,a),D(b,C("smul",mu,b)));
                var x=C("add",a,nu); var y=C("add",C("smul",mu,b),omega);
                var twice=C("mul",N(2),mu);
                result=And(Eq(Q(x),C("subtract",C("smul",mu,
                    C("subtract",C("one",M),C("pow",Q(b),N(2)))),Q(D(a,b)))),
                    And(Eq(Q(y),C("smul",twice,Q(b))),
                        Eq(C("apply",q,D(x,y)),C("smul",twice,C("apply",q,D(a,b))))));
            }
            if (completion == 2)
                result=Eq(C("mul",C("subtract",C("pow",Q(b),N(2)),C("one",M)),Q(D(a,b))),N(0));
            if (completion >= 2) assumptions=And(assumptions,C("DenseRange",q));
            conclusion=All("a",E,All("b",E,All("mu",real,Imp(scalar,result))));
        }
        var body=All("O",C("OriginalData",A,E,P),All("q",C("LinearMap",real,E,C("selfAdjoint",M)),Imp(assumptions,conclusion)));
        return All("A",I("Type"),All("E",I("Type"),All("P",I("Type"),All("n",I("Type"),Seq(
            OpenBracket,C("CStarAlgebra",A),CloseBracket,OpenBracket,C("PartialOrder",A),CloseBracket,
            OpenBracket,C("NormedAddCommGroup",E),CloseBracket,
            OpenBracket,C("NormedSpace",real,E),CloseBracket,OpenBracket,C("Fintype",n),CloseBracket,
            OpenBracket,C("DecidableEq",n),CloseBracket,body)))));
    }
}
