using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class DivisionFreeSchurDocument : IScribeDocumentDefinition
{
    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name,params Formula[] args) => new Formula.Apply(Id(name),[.. args]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula All(string name,Formula type,Formula body) =>
        Seq(Forall,Sp,Par(Seq(Id(name),Colon,type)),Comma,Sp,body);
    private static Formula And(Formula a,Formula b) => Seq(Par(a),Land,Sp,Par(b));
    private static Formula Imp(Formula a,Formula b) => Seq(Par(a),Rightarrow,Sp,b);
    private static Formula Real => Seq(Mathbb,Grp(Id("R")));
    private static Formula Mat(string i,string j) => Call("Matrix",Id(i),Id(j),Real);
    private static Formula Statement(bool mixed)
    {
        var K0=Id("K0");var K1=Id("K1");var v=Id("v");var U=Id("U");
        var conclusion=mixed ? Call("PosSemidef",Call("mixed",K0,K1,v,U)) :
            Call("PosSemidef",Call("schur",K0,v,U));
        var body=All("v",Seq(Id("I"),Rightarrow,Real),All("U",Mat("I","J"),conclusion));
        body=mixed ? All("K0",Mat("I","I"),All("K1",Mat("I","I"),
            Imp(And(Call("PosSemidef",K0),Call("PosSemidef",K1)),body))) :
            All("K0",Mat("I","I"),Imp(Call("PosSemidef",K0),body));
        return All("I",Id("Type"),All("J",Id("Type"),
            Seq(OpenBracket,Call("Fintype",Id("I")),CloseBracket,Sp,
                OpenBracket,Call("Fintype",Id("J")),CloseBracket,Sp,body)));
    }
    private static DocumentBlock Desc(string name,string title,bool mixed,string prose) =>
        Describe.Lean(DescribeId.Create("division-free-"+name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/DivisionFreeSchur."+name),H(title),
            StatementSource.FromAuthor(Disp(Statement(mixed))),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Undivided Schur minors and mixed polarization preserve positivity on arbitrary finite real matrix carriers.",
        H("Division-free PSD compression"),Blocks(
            Desc("schur_posSemidef","Undivided Schur positivity",false,
                "For arbitrary finite types I,J, a real PSD matrix K on I, any real vector v on I and any real rectangular matrix U from J to I, set q=v^T K v, d=U^T K U and b=U^T K v. Then schur(K,v,U)=q d-b b^T is PSD. The quadratic-discriminant inequality gives (v^T K w)^2 <= (v^T K v)(w^T K w), including zero pivot. Substituting w=Uz proves the quadratic-form assertion. Hermitian symmetry is retained. Neither a positive pivot nor nonempty carriers nor injectivity of U is assumed."),
            Desc("mixed_posSemidef","Mixed polarization across two PSD matrices",true,
                "For arbitrary finite types I,J, real PSD matrices K0,K1 on I and the same v,U, write q_s=v^T K_s v, d_s=U^T K_s U and b_s=U^T K_s v. Then mixed(K0,K1,v,U)=q0 d1+q1 d0-b0 b1^T-b1 b0^T is PSD. For a test vector z, Cauchy-Schwarz bounds beta_s^2 by q_s delta_s, where beta_s=v^T K_s Uz and delta_s=(Uz)^T K_s Uz. Put E=q0 delta1+q1 delta0. All q_s,delta_s are nonnegative and E^2-4 beta0^2 beta1^2=(q0 delta1-q1 delta0)^2+4(q0 q1 delta0 delta1-beta0^2 beta1^2)>=0. Since E>=0 this gives E>=2 beta0 beta1, without division. Both zero-pivot and empty-carrier cases remain covered. The two matrices need no common factorization. RankFourLength28Purity uses this cross-matrix positivity as well as both individual Schur matrices."))));
}
