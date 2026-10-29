using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class FiniteSourceCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The uniformly weighted original finite sources have the original biased boundary mean and covariance as norm limits.",
        H("Finite Source Covariance Convergence"), Blocks(
            Def("one", "For every natural n, one(n) is the constant one in L2(mu(n)), where mu(n) gives every actual occurrence mass 1/N(n). Root, internal and terminal occurrences all participate."),
            Def("v", "For every natural n, v(n) is the adjoint of the original finite path map J(n), applied to one(n). It lies in the common real ell2 of nonempty Bool addresses."),
            Def("B", "For every natural n, B(n) is J(n)*J(n) on the common edge ell2. The node L2 codomain of J(n) depends on n."),
            Def("Sigma", "For every natural n, Sigma(n) is B(n) minus rankOne(v(n),v(n)). The rank-one map sends z to the inner product of v(n) with z, multiplied by v(n)."),
            Describe.Lean(DescribeId.Create("finitesourcecovariance-convergence"),
                DeclarationHandle.Create(Prefix + "finite_source_covariance_convergence"),
                H("Simultaneous Norm Limits"), StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every positive real epsilon there is one natural N such that every n at least N satisfies all three norm bounds. The finite objects use the original all-occurrence law and the original cardinality N(n). The boundary objects are precisely those of BiasedBoundaryTrace and BiasedBoundaryFreeRootForm, with a equal to the inverse golden ratio and b equal to its inverse square. False is L and true is R.")),
                    Paragraph(Text("The original path maps ignore absent edges and vanish at the root. The definitions include the singleton sources n=0 and n=1. The claim compares the mean vectors and operators on the common edge Hilbert space; it requires no identification of the changing node spaces.")),
                    Paragraph(Text("The exact node cardinality and Fibonacci formula give convergence of every fixed descendant mass. Comparable addresses have Gram entry equal to the mass of the longer address; incomparable addresses have entry zero. These identities hold for absent addresses as well.")),
                    Paragraph(Text("For a fixed depth h the coordinate projection has finite support. Its mean block is the sum of descendant masses times unit edge vectors, and its Gram block is the double sum of Gram coefficients times coordinate rank-one maps. The finite blocks therefore converge in norm.")),
                    Paragraph(Text("The Hardy remainders are dK(h)=sqrt(2*goldenRatio*a^(h+1)/(1-a)) and dOne(h)=sqrt(a^(h+1)/(1-a)). The mean error is at most dK(h)+dOne(h) plus the finite mean-block error. The Gram error is at most 2*dK(0)*dK(h)+2*dOne(0)*dOne(h) plus the finite Gram-block error. Choose h first and then the common source threshold. Continuity of rankOne gives the centered covariance limit.")),
                    Paragraph(Text("This result states the three norm limits. It supplies no finite counting-screening resolvent identity."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("finitesourcecovariance-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [..xs]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula Ex(string s, Formula t, Formula x) => Seq(Exists, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Implies, Sp, Par(y));
    private static Formula And(Formula x, Formula y) => Seq(Par(x), Sp, Land, Sp, Par(y));
    private static Formula Lt(Formula x, Formula y) => Seq(x, Sp, F.Lt, Sp, y);
    private static Formula Sub(Formula x, Formula y) => Seq(Par(x), Sp, Minus, Sp, Par(y));
    private static Formula Norm(Formula x) => Seq(Vert, Sp, x, Sp, Vert);
    private static Formula ResultFormula()
    {
        Formula n=V("n"), k=V("N"), epsilon=V("epsilon");
        Formula real=Seq(Mathbb,Grp(V("R"))), nat=Seq(Mathbb,Grp(V("N")));
        Formula meanError=Norm(Sub(Call("v",n),Call("BiasedBoundaryFreeRootForm.v")));
        Formula gramTarget=Call("comp",Call("adjoint",Call("BiasedBoundaryTrace.J")),Call("BiasedBoundaryTrace.J"));
        Formula gramError=Norm(Sub(Call("B",n),gramTarget));
        Formula sigmaError=Norm(Sub(Call("Sigma",n),Call("BiasedBoundaryFreeRootForm.Sigma")));
        Formula errors=And(Lt(meanError,epsilon),And(Lt(gramError,epsilon),Lt(sigmaError,epsilon)));
        return All("epsilon",real,Imp(Lt(D(0),epsilon),Ex("N",nat,
            All("n",nat,Imp(Seq(k,Sp,Leq,Sp,n),errors)))));
    }
}
