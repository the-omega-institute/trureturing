using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundarySpectralFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual paired real Hilbert bases identify the original free-root energy on every vector of its form domain.",
        H("The Actual Boundary Spectral Form"), Blocks(
            Describe.Lean(DescribeId.Create("biasedboundaryspectralform-energy"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySpectralForm.actual_spectral_form_energy"),
                H("Weighted Energy and Spectral Support on the Original Form Domain"),
                StatementSource.FromAuthor(EnergyFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("There exist paired Hilbert bases b of the actual centered boundary space G0 and k of the actual effective increment space K. Their positive covariance eigenvalues mu decrease to zero, their reciprocals increase to infinity, and every positive covariance cutoff has only finitely many indices. The original boundary operator graph contains each pair consisting of b(i) and its reciprocal-eigenvalue multiple. The original Sigma and C send k(i) respectively to mu(i) times k(i) and sqrt(mu(i)) times b(i).")),
                    Paragraph(Text("For every F in the original free-root form domain D, let z be its attained least increment lift in K and let f(i) be the b coefficient of Pi(F). Applying the original adjoint to the paired basis identity gives C-adjoint(b(i))=sqrt(mu(i))*k(i). Consequently f(i)=sqrt(mu(i)) times the k coefficient of z. This statement concerns every form-domain vector, without assuming membership in the operator domain.")),
                    Paragraph(Text("Parseval in K identifies the sum of the squared increment coefficients with the squared norm of z, which is the original minimum energy. Positivity of each mu(i) then gives the summable energy series f(i) squared divided by mu(i). HasSum records both summability and equality with the original energy.")),
                    Paragraph(Text("Fix any real threshold lam. If every coefficient with reciprocal mu(i) strictly less than lam vanishes, each remaining weighted energy term is at least lam times f(i) squared. Parseval in G0 and comparison of these convergent series therefore give energy(F) at least lam times the squared norm of Pi(F). Equality at the spectral threshold is included in the retained support, and repeated eigenvalues are unrestricted.")),
                    Paragraph(Text("The bases and eigenvalues are obtained from the actual positive spectral exhaustion of the original biased boundary operator. J, Pi, C, Sigma, K, D and the free-root minimum energy retain their original meanings. This representation supplies the form-support estimate for the lower variational counting argument; it does not itself identify all finite spectral cutoff dimensions or assert the global counting bounds."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula All(string s, Formula type, Formula x) => Seq(Forall,Sp,V(s),Colon,Sp,type,Comma,Sp,Par(x));
    private static Formula Ex(string s, Formula type, Formula x) => Seq(Exists,Sp,V(s),Colon,Sp,type,Comma,Sp,Par(x));
    private static Formula Sq(Formula x) => Seq(Par(x),Caret,Grp(D(2)));
    private static Formula SqNorm(Formula x) => Sq(Seq(Vert,Sp,x,Sp,Vert));
    private static Formula And(params Formula[] xs) => Seq([.. xs.SelectMany((x,i) =>
        i == 0 ? new[] { Par(x) } : new[] { Land, Sp, Par(x) })]);
    private static Formula EnergyFormula()
    {
        Formula b=V("b"), k=V("k"), mu=V("mu"), i=V("i"), f=V("F"), lam=V("lam");
        Formula fv=Call("val",f), bi=Call("val",Call("apply",b,i)), ki=Call("val",Call("apply",k,i));
        Formula mui=Call("apply",mu,i), inv=Seq(Par(mui),Caret,Grp(Seq(Minus,D(1))));
        Formula coeff=Call("apply",Call("repr",b,Call("centeredSubtype",Call("Pi",fv))),i);
        Formula positivity=All("i",Call("Nat"),Seq(D(0),Lt,Sp,mui));
        Formula inverseFunction=Seq(LambdaLower,Sp,i,Colon,Sp,Call("Nat"),Comma,Sp,inv);
        Formula graph=All("i",Call("Nat"),Seq(Call("pair",bi,Call("smul",inv,bi)),InMacro,Sp,Call("graph",Call("boundaryOperator"))));
        Formula edge=All("i",Call("Nat"),Seq(Call("Sigma",ki),Eq,Call("smul",mui,ki)));
        Formula paired=All("i",Call("Nat"),Seq(Call("C",ki),Eq,Call("smul",Call("sqrt",mui),bi)));
        Formula cut=All("eps",Call("Real"),Seq(D(0),Lt,Sp,V("eps"),Implies,Sp,
            Call("Finite",Call("setOf",Seq(LambdaLower,Sp,i,Colon,Sp,Call("Nat"),Comma,Sp,V("eps"),Leq,Sp,mui)))));
        Formula series=All("F",Call("D"),Call("HasSum",
            Seq(LambdaLower,Sp,i,Colon,Sp,Call("Nat"),Comma,Sp,Sq(coeff),Slash,mui),Call("energy",fv)));
        Formula vanish=All("i",Call("Nat"),Seq(inv,Lt,Sp,lam,Implies,Sp,coeff,Eq,D(0)));
        Formula support=All("lam",Call("Real"),All("F",Call("D"),
            Seq(Par(vanish),Implies,Sp,lam,Cdot,Sp,SqNorm(Call("Pi",fv)),Leq,Sp,Call("energy",fv))));
        Formula body=And(positivity,Call("Antitone",mu),Call("Tendsto",mu,Call("atTop"),Call("nhds",D(0))),
            Call("Monotone",inverseFunction),Call("Tendsto",inverseFunction,Call("atTop"),Call("atTop")),
            graph,edge,paired,cut,series,support);
        return Ex("b",Call("HilbertBasis",Call("Nat"),Call("Real"),Seq(V("G"),Underscore,D(0))),
            Ex("k",Call("HilbertBasis",Call("Nat"),Call("Real"),Call("K")),
                Ex("mu",Seq(Call("Nat"),To,Call("Real")),body)));
    }
}
