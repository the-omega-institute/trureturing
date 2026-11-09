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
                Paragraph(Text("The Hilbert product uses the square-sum norm, rather than the maximum product norm. Closedness of K supplies its Hilbert completeness. No finite dimension, separability, spectral basis, compactness of either operator, or identification of the represented algebra with all bounded operators is required. The conclusion is a mathematical operator decomposition; it supplies no additional original response identity or physical operation."))),
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
        return All("H",C("Type"),Inst(C("NormedAddCommGroup",Hh),
            Inst(C("InnerProductSpace",complex,Hh),Inst(C("CompleteSpace",Hh),
            Inst(C("Nontrivial",Hh),All("X",op,All("Y",op,
            Imp(C("IsSelfAdjoint",X),Imp(C("IsSelfAdjoint",Y),All("r",real,All("s",real,
                Imp(assumptions,result)))))))))));
    }
}
