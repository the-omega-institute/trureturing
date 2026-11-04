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
