using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PauliMultiplicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero Hilbert multiplicity space simultaneously diagonalizes and exchanges two anticommuting self-adjoint axes with positive scalar-square radii.",
        H("Simultaneous coordinates on an arbitrary complex Hilbert space"),
        Blocks(Describe.Lean(DescribeId.Create("pauli-multiplicity"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PauliMultiplicity.exists_pauli_multiplicity"),
            H("A closed nonzero multiplicity space and one unitary"),
            StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H be any nonzero complete complex inner product space. The bounded self-adjoint operators X and Y satisfy X squared equals r squared times the identity, Y squared equals s squared times the identity, and XY equals minus YX, with positive real r and s. There is a closed nonzero complex subspace K of this same H and a complex linear isometric equivalence U from the Hilbert product K plus K onto H. For each pair (u,v), U(u,v)=u+Y(v)/s, XU(u,v)=U(r u,-r v), and YU(u,v)=U(s v,s u). Thus the two actions use the same coordinates and retain their respective scalar radii.")),
                Paragraph(Text("Normalize the axes as n=X/r and m=Y/s. The multiplicity space is the kernel of n minus the identity. Its closedness gives completeness and the ordinary orthogonal decomposition H=K plus the orthogonal complement of K. Symmetry of n makes that orthogonal complement invariant. The vector z+n(z) lies both in K and in its orthogonal complement, so n(z)=-z there. Anticommutation then sends K into its orthogonal complement by m and sends that complement back into K. Symmetry and m squared equal to the identity make this restriction an onto isometry. Composing this restricted isometry with the Hilbert orthogonal decomposition constructs U. Surjectivity and nonzero H force K to be nonzero.")),
                Paragraph(Text("The Hilbert product uses the square-sum norm, rather than the maximum product norm. Closedness of K supplies its Hilbert completeness. No finite dimension, separability, spectral basis, compactness of either operator, or identification of the represented algebra with all bounded operators is required. The conclusion is a mathematical operator decomposition; it supplies no additional original response identity or physical operation.")),
                Paragraph(Text("An algebraic application concerns common coefficients on actual reflection frames. For any universe u, let A : Type u have Ring A, StarRing A, Algebra Real A and Nontrivial A instances. Write Frame(A) for all ordered pairs F=(h_F,e_F) of elements of this one A such that star(h_F)=h_F, star(e_F)=e_F, h_F*h_F=e_F*e_F=1 and h_F*e_F=-(e_F*h_F). The scalar action is the real algebra action. No StarModule instance, norm, finite dimension, positivity, CAR presentation or analytic regularity is assumed. Every admissible pair belongs to the domain; it is not restricted to a chosen matrix stage or finite family.")),
                Paragraph(Text("For every function s : Frame(A) -> Real, assume that for every F,G in Frame(A), (s(F)-s(G)) • (h_F*h_G-h_G*h_F)=0 in A. Then for every F,G in Frame(A), s(F)=s(G). The coefficients can be arbitrary real numbers. This pairwise conclusion also holds when Frame(A) is empty, without selecting a base frame. If a frame F0 exists, the common value is s(F0); obtaining a sign requires the separate source condition that the local coefficients lie in {1,-1}.")),
                Paragraph(Text("Here is the complete algebraic derivation. If h_F*h_G differs from h_G*h_F, its difference is nonzero. Mathlib's smul_eq_zero applied to the assumed overlap gives s(F)-s(G)=0, hence s(F)=s(G). This scalar cancellation uses the real vector space structure supplied by Algebra Real A; it does not assert that the ring A has no zero divisors.")),
                Paragraph(Text("Two anticommuting involutions a,b cannot commute in this nontrivial real algebra. Otherwise ab=ba and ab=-ba give ab=-ab, so (2 : Real) • (ab)=ab+ab=0. Since 2 is nonzero, smul_eq_zero gives ab=0. Associativity and a*a=b*b=1 then give 1=a*(a*b)*b=0, contradicting one_ne_zero. The argument needs no selfadjointness or compatibility between star and scalar multiplication.")),
                Paragraph(Text("For each frame F define its swap F'=(e_F,h_F). Its axes remain selfadjoint involutions, and e_F*h_F=-(h_F*e_F) follows by negating the original anticommutation equality. Thus F' is an actual frame of the same A. The preceding noncommutation argument applies to h_F,e_F, so the overlap for F,F' yields s(F)=s(F'). Likewise s(G)=s(G') for G'=(e_G,h_G).")),
                Paragraph(Text("There are four possible cross pairs to test. If h_F,h_G do not commute, direct cancellation gives s(F)=s(G). If e_F,h_G do not commute, cancellation for F',G gives the path s(F)=s(F')=s(G). If h_F,e_G do not commute, cancellation for F,G' gives s(F)=s(G')=s(G). If e_F,e_G do not commute, cancellation for F',G' gives s(F)=s(F')=s(G')=s(G). These cases cover every pair for which at least one cross pair fails to commute.")),
                Paragraph(Text("In the remaining case all four cross pairs commute. Put p=e_F*e_G and B=(p,h_F), using actual elements of A. Reversal of products under star gives star(p)=star(e_G)*star(e_F)=e_G*e_F=e_F*e_G=p. Cross commutation and associativity give p*p=(e_F*e_G)*(e_F*e_G)=(e_F*e_F)*(e_G*e_G)=1. The other axis h_F is already a selfadjoint involution.")),
                Paragraph(Text("The two required anticommutation calculations retain the same product p. First p*h_F=e_F*(e_G*h_F)=(e_F*h_F)*e_G=-(h_F*e_F)*e_G=-(h_F*p), using cross commutation of e_G,h_F and anticommutation inside F. Second p*h_G=e_F*(e_G*h_G)=-e_F*(h_G*e_G)=-(h_G*e_F)*e_G=-(h_G*p), using anticommutation inside G and cross commutation of e_F,h_G. The first equality proves that B=(p,h_F) is an admissible frame. Since p, h_F and h_G square to 1, both displayed anticommutations imply noncommutation by the earlier argument.")),
                Paragraph(Text("The overlap hypothesis therefore applies to the actual pairs B,F and B,G and yields s(B)=s(F) and s(B)=s(G). Consequently s(F)=s(B)=s(G), completing also the all-commuting case. The product construction and coefficient paths are elementary consequences of the stated relations and scalar cancellation. The Hilbert multiplicity theorem above concerns the same kind of anticommuting selfadjoint axes when represented by bounded Hilbert operators; its unitary decomposition is a related result, and is not a premise of this purely algebraic inference.")),
                Paragraph(Text("The source correspondence is the common-sign step of section 61.1 of docs/develop/theory/AURIC_ORIGINAL_ATOMIC_SEPARATION_AND_PB_RECONSTRUCTION_CONTINUATION.md. Its given unital complex CAR algebra is viewed as a real algebra with its existing ring and star-ring structures. Each actual source pair h,e maps to F=(h,e) in the full frame domain. Once the source has supplied the local rows, s(F) is their local coefficient from the same original total response D : E x E -> E, where E=A_sa; in the source notation it is sigma_(B_F) for the actual unital M2 subalgebra generated by h,e. The local formula to supply is D(R*h,b)=(i*s(F)/2)*[R*h,b] for every real R and every original selfadjoint b. Its overlap equation must hold for every two such actual frames, including swapped frames and the product frame B above. After translating that equation to the real scalar action, the proved cancellation gives equality of those local coefficients. The source's {1,-1}-valuedness and an actual frame, supplied there by the first tensor factor, are additionally needed to select one ordinary common sign.")),
                Paragraph(Text("The local reflection rows, their real sign coefficients and the overlap law remain obligations of the original source: they must be derived from the same total D with all of section 59.1's A1-A3, P2 and complete PB assumptions, including the actual product frame. In that source A is given, the Jordan product is (ab+ba)/2, the cone is A_+, the unit is 1, and the norm and the same positive real linear evaluation family separate the selfadjoint part and determine the cone. The original labels and every evaluation mass, including zero, unequal, subnormalized and nonnormal evaluations in the original representation, stay in scope. No additivity, homogeneity, continuity, measurability, covariance, unit translation, output closure, quotient descent or bidual extension of D is an extra premise paid by this algebraic argument. Naming the product frame does not supply any of these source bridges.")),
                Paragraph(Text("The full CAR trace, scalar center and conditional expectations, finite spectral windows, nonreducing rectangle identities with both error terms, the complete N-1 trace budget, exact finite-phase transport and fixed-output polar approximation remain unproved source obligations in this application. Preparation, actual joint-process and instrument realizations, legal future returns and physical-clock contracts are likewise not supplied. The parent atom a99c61a4dfef9c0da9bfaa61d63db8e090c15c5ca527bfb378264ea18b73820c remains open; this application neither covers that parent nor establishes the global CAR classification. The separate full-family source-binding issue https://github.com/the-omega-institute/trureturing/issues/28676 remains unresolved."))),
            DescribeRole.Theorem))));

    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => global::StrataLint.Scribe.DefinitionDsl.Call(s,a);
    private static Formula N(int n) => global::StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Ex(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(s),t,b);
    private static Formula Eq(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Equal(a,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Inst(Formula a, Formula b) => Seq(OpenBracket,a,CloseBracket,b);
    private static Formula Statement()
    {
        var Hh=I("H"); var X=I("X"); var Y=I("Y"); var r=I("r"); var s=I("s");
        var K=I("K"); var U=I("U"); var p=I("p"); var complex=C("Complex");
        var real=C("Real"); var op=C("ContinuousLinearMap",complex,Hh,Hh);
        var sub=C("Subtype",K); var pair=C("WithLp",N(2),C("Product",sub,sub));
        Formula A(Formula f, Formula x)=>C("apply",f,x);
        Formula Sm(Formula a,Formula x)=>C("smul",a,x);
        Formula Re(Formula a)=>C("ofReal",a);
        Formula Fst()=>C("fst",p);
        Formula Snd()=>C("snd",p);
        Formula Lp(Formula a,Formula b)=>C("toLp",N(2),C("pair",a,b));
        var laws=And(All("p",pair,Eq(A(U,p),C("Add",C("val",Fst()),
                    Sm(C("Inverse",Re(s)),A(Y,C("val",Snd())))))),
            And(All("p",pair,Eq(A(X,A(U,p)),A(U,Lp(Sm(Re(r),Fst()),Sm(C("Negate",Re(r)),Snd()))))),
                All("p",pair,Eq(A(Y,A(U,p)),A(U,Lp(Sm(Re(s),Snd()),Sm(Re(s),Fst())))))));
        var result=Ex("K",C("Submodule",complex,Hh),And(C("IsClosed",C("SetOfSubmodule",K)),
            And(C("Nontrivial",sub),Ex("U",C("LinearIsometryEquiv",complex,pair,Hh),laws))));
        var assumptions=And(C("Lt",N(0),r),And(C("Lt",N(0),s),
            And(Eq(C("Multiply",X,X),Sm(Re(C("pow",r,N(2))),C("One",op))),
            And(Eq(C("Multiply",Y,Y),Sm(Re(C("pow",s,N(2))),C("One",op))),
                Eq(C("Multiply",X,Y),C("Negate",C("Multiply",Y,X)))))));
        var axes=All("X",op,All("Y",op,Imp(C("IsSelfAdjoint",X),
            Imp(C("IsSelfAdjoint",Y),All("r",real,All("s",real,Imp(assumptions,result)))))));
        var instances=Inst(C("NormedAddCommGroup",Hh),Inst(C("InnerProductSpace",complex,Hh),
            Inst(C("CompleteSpace",Hh),Inst(C("Nontrivial",Hh),axes))));
        return All("H",C("Type"),instances);
    }
}
