using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class RankOneInvariantMetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive invariant metric and a centralizer line force dimension one or three.",
        H("Rank-One Centralizers in Real Metric Lie Algebras"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimum-frequency-frame"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/RankOneInvariantMetric.min_frame"),
                H("An orthonormal frame at the minimum positive frequency"),
                StatementSource.FromAuthor(MinFrameFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let L be a finite-dimensional real inner product space and br a bilinear operation on L. Assume br(z,z)=0 and the derivation identity br(x,br(y,z))=br(br(x,y),z)+br(y,br(x,z)) for every x,y,z. Fix a unit vector a. Assume the inner product is invariant, in the precise form inner(br(x,y),z)=-inner(y,br(x,z)), that every z with br(a,z)=0 is a real multiple of a, and that the linear map br(a) is nonzero.")),
                    Paragraph(Text("There are a positive real number m and unit vectors u,v such that a,u,v are pairwise orthogonal, br(a,u)=m v, br(a,v)=-m u, and br(u,v)=m a. Moreover, m is the least positive rotation frequency: for every positive real q and every nonzero x with br(a,br(a,x))=-(q squared)x, one has m at most q. The finite spectral decomposition supplies a minimum positive frequency and a unit eigenvector; invariance, the derivation identity and the centralizer condition determine the third bracket."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finrank-eq-one-or-three"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/RankOneInvariantMetric.finrank_eq_one_or_three"),
                H("The dimension dichotomy"),
                StatementSource.FromAuthor(DimensionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let K be an arbitrary finite-dimensional real Lie algebra. The value B is an InnerProductSpace.Core: its real inner product is positive definite, symmetric and bilinear, with the underlying additive group and real module those of the given Lie algebra. Assume B([x,y],z)=-B(y,[x,z]) for every x,y,z. Let a be nonzero and assume every z commuting with a is a real multiple of a. Since [a,a]=0, this is exactly the assertion that the centralizer of a is its real span. Then the real dimension of K is one or three.")),
                    Paragraph(Text("When ad(a) vanishes, the centralizer condition already makes K the span of a. Otherwise normalize a and apply the frozen skew_paired_basis_induction to ad(a) direct-summed with itself on WithLp 2 (K times K). This doubled space has even dimension regardless of the dimension of K. A minimum positive paired frequency and a nonzero original-coordinate component provide a unit vector u. Set v=ad(a)u/mu. Invariance and Jacobi give an orthonormal triple a,u,v with [a,u]=mu v, [a,v]=-mu u and [u,v]=mu a.")),
                    Paragraph(Text("The span S of this actual triple is a Lie subalgebra, and its orthogonal complement M in the same K is S-stable. Complexify S and M. The normalized elements h=(2i/mu)a, e=(u+iv)/mu, f=(-u+iv)/mu form an sl2 triple. Mathlib IsSl2Triple.exists_hasPrimitiveVectorWith constructs a primitive vector in every nonzero finite-dimensional complex module. Its existing exists_nat, pow_toEnd_f_ne_zero_of_eq_nat and lie_h_pow_toEnd_f give a nonzero vector of h-weight zero or one. The proof directly applies these results, without reproving the ladder.")),
                    Paragraph(Text("Weight zero has real and imaginary parts in the centralizer of a and in S-perp, so both vanish. Weight one has a nonzero real or imaginary part x with ad(a) squared applied to x equal to -(mu/2) squared times x, contradicting minimality of mu. Thus M is zero and S is all of K. The orthonormal triple then gives dimension three. This complement obstruction is the substantive step beyond the reused spectral and sl2 suppliers.")),
                    Paragraph(Text("This algebraic theorem supplies the dimension lemma used by the one-point reciprocity argument. To apply it to a compact effective matrix group requires a positive invariant metric on its actual Lie algebra and the derivation of the centralizer line from the entire quotient relation. The original-group exponential bridge, exclusion of the one-dimensional alternative in that application, equality with the orthogonal Lie algebra, identity-component and SO/O classification, and the reverse quotient-relation implication are separate obligations. The dimension lemma alone asserts none of those group conclusions."))),
                DescribeRole.Theorem))));

    private static Formula Bracket(Formula x, Formula y) => Seq(OpenBracket, x, Comma, y, CloseBracket);
    private static Formula Pair(Formula b, Formula x, Formula y) => Seq(b, Open, x, Comma, y, Close);

    private static Formula MinFrameFormula()
    {
        Formula l = F.Id("L"), br = F.Id("br"), a = F.Id("a");
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z"), c = F.Id("c");
        Formula m = F.Id("m"), u = F.Id("u"), v = F.Id("v"), q = F.Id("q");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula zero = D(0), one = D(1);
        Formula assumptions = Seq(
            Open, Forall, Sp, z, Colon, Sp, l, Comma, Esc, Pair(br,z,z), Eq, zero, Close,
            Sp, Land, Sp,
            Open, Forall, Sp, x, Comma, y, Comma, z, Colon, Sp, l, Comma, Esc,
                Pair(br,x,Pair(br,y,z)), Eq,
                Pair(br,Pair(br,x,y),z), Plus, Pair(br,y,Pair(br,x,z)), Close,
            Sp, Land, Sp, Call("norm",a), Eq, one, Sp, Land, Sp,
            Open, Forall, Sp, x, Comma, y, Comma, z, Colon, Sp, l, Comma, Esc,
                Call("inner",Pair(br,x,y),z), Eq, Minus, Call("inner",y,Pair(br,x,z)), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, z, Colon, Sp, l, Comma, Esc,
                Pair(br,a,z), Eq, zero, Sp, Rightarrow, Sp,
                Exists, Sp, c, Colon, Sp, real, Comma, Esc, z, Eq, c, Cdot, Sp, a, Close,
            Sp, Land, Sp, br, Open, a, Close, Neq, Sp, zero);
        Formula conclusion = Seq(
            Exists, Sp, m, Colon, Sp, real, Comma, Esc,
            Exists, Sp, u, Comma, v, Colon, Sp, l, Comma, Esc,
            zero, Lt, m, Sp, Land, Sp, Call("norm",u), Eq, one,
            Sp, Land, Sp, Call("norm",v), Eq, one,
            Sp, Land, Sp, Call("inner",a,u), Eq, zero,
            Sp, Land, Sp, Call("inner",a,v), Eq, zero,
            Sp, Land, Sp, Call("inner",u,v), Eq, zero,
            Sp, Land, Sp, Pair(br,a,u), Eq, m, Cdot, Sp, v,
            Sp, Land, Sp, Pair(br,a,v), Eq, Minus, m, Cdot, Sp, u,
            Sp, Land, Sp, Pair(br,u,v), Eq, m, Cdot, Sp, a,
            Sp, Land, Sp,
            Open, Forall, Sp, q, Colon, Sp, real, Comma, Esc,
                Forall, Sp, x, Colon, Sp, l, Comma, Esc,
                zero, Lt, q, Sp, Land, Sp, x, Neq, Sp, zero, Sp, Land, Sp,
                Pair(br,a,Pair(br,a,x)), Eq, Minus, q, Caret, Grp(D(2)), Cdot, Sp, x,
                Sp, Rightarrow, Sp, m, Leq, Sp, q, Close);
        return Disp(Seq(
            Forall, Sp, l, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Call("NormedAddCommGroup",l), CloseBracket, Comma, Esc,
            OpenBracket, Call("InnerProductSpace",real,l), CloseBracket, Comma, Esc,
            OpenBracket, Call("FiniteDimensional",real,l), CloseBracket, Comma, Esc,
            br, Colon, Sp, Call("LinearMap",real,l,Call("LinearMap",real,l,l)), Comma, Esc,
            a, Colon, Sp, l, Comma, Esc,
            Open, assumptions, Close, Sp, Rightarrow, Sp, conclusion));
    }

    private static Formula DimensionFormula()
    {
        Formula k = F.Id("K"), b = F.Id("B"), a = F.Id("a");
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z"), c = F.Id("c");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula dim = Seq(Operatorname, Grp(F.Id("finrank")), Underscore, Grp(real), Open, k, Close);
        return Disp(Seq(
            Forall, Sp, k, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Call("LieRing", k), CloseBracket, Comma, Esc,
            OpenBracket, Call("LieAlgebra", real, k), CloseBracket, Comma, Esc,
            OpenBracket, Call("FiniteDimensional", real, k), CloseBracket, Comma, Esc,
            b, Colon, Sp, Call("InnerProductSpaceCore", real, k), Comma, Esc,
            a, Colon, Sp, k, Comma, Esc,
            Open, Forall, Sp, x, Comma, y, Comma, z, Colon, k, Comma, Esc,
                Pair(b, Bracket(x,y), z), Eq, Minus, Pair(b,y,Bracket(x,z)), Close, Sp, Land, Sp,
            a, Neq, D(0), Sp, Land, Sp,
            Open, Forall, Sp, z, Colon, k, Comma, Esc,
                Bracket(a,z), Eq, D(0), Sp, Rightarrow, Sp,
                Exists, Sp, c, Colon, real, Comma, Esc, z, Eq, c, Cdot, Sp, a, Close,
            Sp, Rightarrow, Sp, dim, Eq, D(1), Sp, Lor, Sp, dim, Eq, D(3)));
    }
}
