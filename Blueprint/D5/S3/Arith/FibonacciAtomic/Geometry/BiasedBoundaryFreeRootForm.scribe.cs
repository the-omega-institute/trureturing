using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryFreeRootFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The infinite path trace on the fixed biased boundary has compact covariance. The original free-root energy infimum is attained in the effective increment space, and its weak variational graph is determined by the actual covariance.",
        H("Actual Covariance and the Free-Root Form"), Blocks(
            Def("v", "The vector v is the adjoint of the actual bounded path trace J applied to the constant one in G=L2(M). The biased product measure and the infinite square-summable increment space are fixed throughout."),
            Def("Sigma", "Sigma=C* C acts on the original infinite increment space H, where C=Pi J is included in the original ambient G. Taking this ambient adjoint is the same as extending the adjoint from the mean-zero boundary subspace by zero on constants."),
            Def("K", "K is the orthogonal complement of the kernel of Sigma. Vectors in the edge kernel are excluded from this effective increment space."),
            Result("mean_indicator", "Mean of a Boundary Cylinder Indicator", All("p",V("Edge"),Seq(Call("mean",Call("indicator",V("p"))),Eq,Call("Mreal",Call("cylinder",Call("val",V("p"))))))),
                "For every nonempty edge address p, the mean of its original boundary cylinder indicator is the real measure M([p]). The mean and indicator use the same biased boundary measure M.",
                "Applying the cylinder mass formula gives the corresponding edge coordinate of v=J*1. These coordinates identify the limiting mean vector and distinguish its nonzero boundary values."),
            Result("actual_compact_covariance", "Compact Trace and Actual Covariance", CompactFormula(),
                "For every positive epsilon, choose a stopping threshold at most both one half and epsilon squared divided by four times the golden ratio. The all-vector stopping residual bounds the operator norm of C minus Qt C by epsilon over two. The actual stopping range is finite dimensional, so norm closure of compact operators gives compactness of C. The difference J-C factors through the one-dimensional constant space; consequently J is compact too, and composing C with its bounded adjoint makes Sigma compact.",
                "Self-adjoint centering and its idempotence give Sigma=J* J-v tensor v. For all z,w in H the bilinear covariance equals the inner product of their actual centered traces. In particular its quadratic form is the squared centered trace norm, and its kernel is exactly the kernel of C. On every pair of original unit edge vectors p,q, its entry is M([p] intersect [q])-M([p])M([q])."),
            Result("mean_Pi", "Centering Has Zero Mean", All("F",V("G"),Seq(Call("mean",Call("Pi",V("F"))),Eq,D(0))),
                "Orthogonal centering subtracts the original integral mean, so every centered boundary vector has mean zero.",
                "This is the mean-zero codomain condition for the actual centered trace."),
            Paragraph(Text("The original BiasedBoundaryCentering.Pi_const identity removes every actual constant. In the free-root form, constants therefore require no effective increment.")),
            Result("Pi_idem", "Idempotent Centering", All("F",V("G"),Seq(Call("Pi",Call("Pi",V("F"))),Eq,Call("Pi",V("F")))),
                "A centered vector already has zero mean, so centering it again leaves it fixed.",
                "This identity identifies covariance graph coordinates with centered boundary vectors."),
            Result("adjoint_mem_K", "The Adjoint Lies in the Effective Edge Space", All("h",V("G"),Seq(Call("adjoint",V("C"),V("h")),InMacro,Sp,V("K"))),
                "Every vector C*h is orthogonal to the original covariance kernel because pairing it with an edge vector z equals pairing h with Cz.",
                "This effective-space inclusion is consumed by the positive eigenspace identification of the original boundary operator."),
            Result("inner_centered", "Pairing with a Mean-Zero Vector", All("h",V("G"),All("F",V("G"),Seq(Call("mean",V("h")),Eq,D(0),Implies,Sp,Par(Seq(Call("inner",V("h"),Call("Pi",V("F"))),Eq,Call("inner",V("h"),V("F"))))))),
                "A vector with zero mean is orthogonal to constants. Its inner product with any centered test vector equals its inner product with the original test vector.",
                "The identity applies to every test vector in the original boundary L2 space."),
            Def("D", "The domain D is exactly the subspace of all F=c times the constant one plus Jz, with arbitrary real root value c and arbitrary z in the original infinite H. No finite-level restriction or replacement measure enters this domain."),
            Def("energy", "For an ambient F in G, energy(F) is the real infimum of the set of squared increment norms over all original representations F=constG(c)+Jz. Its asserted energy interpretation is restricted to F in D, where the set is nonempty and the infimum is attained."),
            Def("lift", "For each F in D, lift(F) is the unique z in K such that Cz=Pi F. Orthogonal projection onto K removes exactly the redundant edge kernel."),
            Result("free_root_least_energy", "Attainment of the Original Energy", EnergyFormula(),
                "For any representation F=constG(c)+Jz, the least increment is the orthogonal projection of z onto K. Projection leaves its centered trace unchanged and decreases its norm. Injectivity of C on K makes this increment independent of the chosen representation and unique in K.",
                "The root coefficient is restored as mean(F)-mean(J lift(F)). This is an actual original representation and attains the infimum, so energy(F)=the squared norm of lift(F). Every other representation is included in the comparison."),
            Def("form", "The form pairing of F and T in D is the real inner product of their least increments. Its diagonal is the original infimum energy, and its value is one quarter of energy(F+T)-energy(F-T), so it is the polarization of that original energy."),
            Def("weakGraph", "The pair (u,h) lies in the weak graph when u belongs to the original D and the form pairing of u with every F in D equals the G inner product of h with F."),
            Def("formSpace", "The form domain in graph coordinates consists exactly of pairs (F,z) in G times the original H with z in K and Cz=Pi F. It is the closed graph of the unique least increment, hence is complete for the inherited product norm. Its increment norm squared is the original energy."),
            Def("formInclusion", "The inclusion of the original form domain into G is the first-coordinate map on formSpace. Its second-coordinate map is the unique least increment."),
            Result("free_root_variational_graph", "The Entire Weak Variational Graph", GraphFormula(),
                "The form diagonal equals the original free-root energy on every element of D. Uniqueness of the effective lift makes it additive and subtractive; the real inner-product polarization identity identifies this pairing with the polarization of the original infimum. The graph of F mapped to (F,lift(F)) is closed in G times H: it is exactly the closed constraint set z in K and Cz=Pi F. In these complete graph coordinates, the actual inclusion equals the compact map C applied to the increment coordinate plus the constant map applied to the mean of the trace coordinate. Thus the original form-domain inclusion is compact. The weak equation holds for all original traces exactly when mean(h)=0 and u=constG(mean(u))+CC*h. Testing constants forces mean(h)=0; testing every Jz identifies the least increment of u with C*h. Conversely C*h belongs to K, and the stated covariance representation satisfies the equation against every F in D.",
                "This module characterizes the entire weak graph without assuming an operator realization. BiasedBoundaryOperator constructs its dense self-adjoint realization, compact resolvent and positive covariance eigenspace identification. The complete ordered spectral sequence, the unitary polar map, its two range-domain identities and global eigenvalue counting require additional arguments."))));

    private static DocumentBlock Def(string name, string prose) => Describe.Lean(
        DescribeId.Create("biasedboundaryfreerootform-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(name), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Result(string name, string title, Formula formula, string first, string second) => Describe.Lean(
        DescribeId.Create("biasedboundaryfreerootform-" + name.Replace("_", "").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(first)), Paragraph(Text(second))), DescribeRole.Theorem);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula NormSq(Formula x) => Seq(Par(Seq(Vert,Sp,x,Sp,Vert)), Caret, Grp(D(2)));
    private static Formula And(params Formula[] xs) => Seq([.. xs.SelectMany((x, i) => i == 0 ? new[] { Par(x) } : new[] { Land, Par(x) })]);
    private static Formula CompactFormula()
    {
        Formula z=V("z"), w=V("w"), sigma=V("Sigma"), c=V("C"), j=V("J"), h=V("H");
        return And(Call("IsCompactOperator",j), Call("IsCompactOperator",c), Call("IsCompactOperator",sigma),
            Seq(sigma,Eq,Call("compose",Call("adjoint",j),j),Minus,Call("rankOne",V("v"),V("v"))),
            All("z",h,All("w",h,Seq(Call("inner",z,Call("Sigma",w)),Eq,Call("inner",Call("C",z),Call("C",w))))),
            All("z",h,Seq(Call("inner",z,Call("Sigma",z)),Eq,NormSq(Call("C",z)))),
            Seq(Call("ker",sigma),Eq,Call("ker",c)),
            All("p",V("Edge"),All("q",V("Edge"),Seq(
                Call("inner",Call("single",D(2),V("p"),D(1)),Call("Sigma",Call("single",D(2),V("q"),D(1)))),Eq,
                Call("Mreal",Call("intersection",Call("cylinder",V("p")),Call("cylinder",V("q")))),Minus,
                Call("product",Call("Mreal",Call("cylinder",V("p"))),Call("Mreal",Call("cylinder",V("q"))))))));
    }
    private static Formula EnergyFormula()
    {
        Formula f=V("F"), z=V("z"), c=V("c"), l=Call("lift",f), h=V("H"), k=V("K");
        Formula rep=Seq(f,Eq,Call("constG",c),Plus,Call("J",z));
        Formula original=Seq(f,Eq,Call("constG",Seq(Call("mean",f),Minus,Call("mean",Call("J",l)))),Plus,Call("J",l));
        return All("F",V("D"),And(Seq(l,InMacro,Sp,k),Seq(Call("C",l),Eq,Call("Pi",f)),original,
            Seq(Call("energy",f),Eq,NormSq(l)),
            All("c",Seq(Mathbb,Grp(V("R"))),All("z",h,Seq(rep,Implies,Sp,Par(And(
                Seq(l,Eq,Call("starProjection",k,z)),Seq(NormSq(l),Leq,NormSq(z))))))),
            All("z",h,Seq(And(Seq(z,InMacro,Sp,k),Seq(Call("C",z),Eq,Call("Pi",f))),Implies,Sp,Seq(z,Eq,l)))));
    }
    private static Formula GraphFormula()
    {
        Formula f=V("F"), u=V("u"), h=V("h"), g=V("G");
        Formula rhs=And(Seq(Call("mean",h),Eq,D(0)),Seq(u,Eq,Call("constG",Call("mean",u)),Plus,Call("C",Call("apply",Call("adjoint",V("C")),h))));
        return And(All("F",V("D"),Seq(Call("form",f,f),Eq,Call("energy",f))),
            All("F",V("D"),All("T",V("D"),Seq(Call("form",f,V("T")),Eq,
                Seq(Frac,Grp(Seq(Call("energy",Seq(f,Plus,V("T"))),Minus,Call("energy",Seq(f,Minus,V("T"))))),Grp(D(4)))))),
            Call("IsClosed",Call("range",Par(Seq(f,Colon,V("D"),Mapsto,Call("pair",f,Call("lift",f)))))),
            All("x",V("formSpace"),Seq(Exists,Sp,f,Colon,V("D"),Comma,Sp,And(
                Seq(V("x"),Eq,Call("pair",f,Call("lift",f))),
                Seq(Call("energy",f),Eq,NormSq(Call("snd",V("x"))))))),
            Call("IsCompactOperator",V("formInclusion")),
            All("u",g,All("h",g,Seq(Call("weakGraph",u,h),Iff,rhs))));
    }
}
