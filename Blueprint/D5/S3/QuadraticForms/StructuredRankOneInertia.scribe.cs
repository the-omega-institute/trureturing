using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class StructuredRankOneInertiaDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/QuadraticForms/StructuredRankOneInertia.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/lucid2026structureddowndate");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structured downdates of real symmetric matrices have exact positive, negative and zero eigenvalue counts, including singular forms.",
        H("Structured rank-one inertia"),
        Blocks(
            Entry("pivot", "Quadratic pivot", Definition("pivot", Delta, Call("dot", X, Call("mulVec", A, X))), DescribeRole.Definition),
            Entry("downdate", "Structured downdate", Definition("downdate", M,
                Seq(A, Sp, Minus, Sp, Call("inv", Delta), Sp, Cdot, Sp,
                    Call("vecMulVec", Call("mulVec", A, X), Call("mulVec", A, X)))), DescribeRole.Definition),
            Entry("zeroIndex", "Zero eigenvalue multiplicity", OverIndex(All(A, Mat, All(V("h"), Call("IsHermitian", A),
                Equal(Call("zeroIndex", V("h")), Count("i", Equal(Call("eigenvalues", V("h"), V("i")), D(0))))))), DescribeRole.Definition),
            Entry("diagonal_counts", "Real diagonal sign counts", OverIndex(All(V("d"), Vec,
                And(Equal(Call("posIndex", Call("isHermitianDiagonal", V("d"))), Count("i", Lt(D(0), Call("d", V("i"))))),
                    Equal(Call("negIndex", Call("isHermitianDiagonal", V("d"))), Count("i", Lt(Call("d", V("i")), D(0))))))), DescribeRole.Theorem),
            Entry("kernel_split", "Exact direct-sum kernel", Assumptions(And(
                Equal(Kernel(M), Call("sup", Kernel(A), Call("span", Real, Singleton(X)))),
                Call("Disjoint", Kernel(A), Call("span", Real, Singleton(X)))),false), DescribeRole.Theorem),
            Entry("nullity_downdate", "Every old null direction and exactly one new direction", Assumptions(
                Equal(Call("finrank", Real, Kernel(M)), Seq(Call("finrank", Real, Kernel(A)), Sp, Plus, Sp, D(1))),false), DescribeRole.Theorem),
            Entry("inertia_downdate", "Both complete inertia triples", Inertia(), DescribeRole.Theorem),
            Paragraph(Text("The index type is any finite type in Type, with a decidable equality; in particular Fin n is allowed for every natural n. A is any real Hermitian matrix, equivalently a real symmetric matrix. Delta=pivot(A,x), w=A x and M=downdate(A,x). The positive and negative indices are RHLinalg's eigenvalue counts with multiplicity. zeroIndex counts exactly the zero eigenvalues with multiplicity. The formulas retain additive identities, so the count decremented in the usual natural-subtraction presentation is proved to be at least one.")),
            Paragraph(Text("The kernel proof writes each v in ker M as v-tx plus tx, where t=Delta-inverse times the dot product of w and v. The first summand lies in ker A. Symmetry makes ker A orthogonal to w, and nonzero Delta makes its intersection with span(x) zero. Rank-nullity and the spectral rank identity identify the kernel dimension with zeroIndex. Thus no null direction of a singular A is lost.")),
            Paragraph(Text("For the other two counts, augment A by one zero coordinate. The upper triangular matrix with upper-right column x transforms diag(A,0) into [[A,w],[w-transpose,Delta]]. A lower triangular matrix with lower-left row -w-transpose/Delta transforms that same form into diag(M,Delta). Both transformers have determinant one. The existing invertible Hermitian inertia theorem applies over the reals. Characteristic-polynomial roots prove block additivity, preserving multiplicities; the real diagonal-count proof uses the real spectral theorem directly, without a complex-to-real identification.")),
            Paragraph(Text("For MO513954 revision 2, substitute A=Matrix.diagonal d. The theorem includes dimension zero vacuously and every positive finite dimension, both pivot signs and singular diagonal matrices. The source author already proposed the hyperplane/direct-sum and block-congruence mechanism. The exact definitions, real spectral-count derivation, kernel and nullity proofs, and complete symmetric-matrix inertia theorem here are repository-derived; the source question and proposed mechanism are acknowledged separately from these completed derivations. These are standard Sylvester inertia arguments, with no ordinary novelty or priority claim. The continuous-family corollary is a separate source obligation; the matrix theorem by itself does not settle the full named question. Audit registration remains unfinished under issue #25408.")))));

    private static DocumentBlock Entry(string name, string title, Formula formula, DescribeRole role) => Describe.Lean(
        DescribeId.Create("structured-rank-one-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(name switch {
            "pivot" => "The pivot is the real quadratic value of the original matrix on x.",
            "downdate" => "The coefficient is exactly the inverse pivot; the original matrix is never inverted.",
            "zeroIndex" => "Zero eigenvalues are counted with multiplicity in the finite Hermitian spectrum.",
            "diagonal_counts" => "Characteristic-polynomial roots identify the real diagonal signs with the exact spectral counts.",
            "kernel_split" => "The equality and disjointness together identify the exact direct sum of old and new null directions.",
            "nullity_downdate" => "The direct sum adds the one-dimensional line spanned by x to the original kernel.",
            _ => "The additive counts include both signs and retain all singular directions."
        }))), role);
    private static Formula V(string s) => F.Id(s);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Index => V("I");
    private static Formula Vec => Seq(Open, Index, Sp, To, Sp, Real, Close);
    private static Formula Mat => Call("Matrix", Index, Index, Real);
    private static Formula A => V("A");
    private static Formula X => V("x");
    private static Formula Delta => Call("pivot", A, X);
    private static Formula M => Call("downdate", A, X);
    private static Formula Kernel(Formula a) => Call("ker", Call("mulVecLin", a));
    private static Formula Typed(Formula x, Formula t) => Seq(Open, x, Sp, Colon, Sp, t, Close);
    private static Formula All(Formula x, Formula t, Formula b) => Seq(Open,Forall, Sp, Typed(x,t), Comma, Sp,b,Close);
    private static Formula Some(Formula x, Formula t, Formula b) => Seq(Open,Exists, Sp, Typed(x,t), Comma, Sp,b,Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula Lt(Formula a, Formula b) => Seq(a,Sp,F.Lt,Sp,b);
    private static Formula And(Formula a, Formula b) => Seq(Open,Open,a,Close,Sp,Land,Sp,Open,b,Close,Close);
    private static Formula Implies(Formula a, Formula b) => Seq(Open,a,Close,Sp,Rightarrow,Sp,Open,b,Close);
    private static Formula Singleton(Formula a) => Seq(OpenBrace,Sp,a,CloseBrace);
    private static Formula Count(string i, Formula p) => Call("card", Seq(OpenBrace,Typed(V(i),Index),Sp,Mid,Sp,p,CloseBrace));
    private static Formula OverIndex(Formula b, bool decidable = true) => All(Index,Call("Type"),Seq(
        OpenBracket,Call("Fintype",Index),CloseBracket,Sp,
        decidable ? Seq(OpenBracket,Call("DecidableEq",Index),CloseBracket,Sp,b) : b));
    private static Formula Definition(string name, Formula lhs, Formula rhs) => OverIndex(All(A,Mat,All(X,Vec,Equal(lhs,rhs))),false);
    private static Formula Assumptions(Formula b, bool decidable = true) => decidable
        ? OverIndex(All(A,Mat,All(V("h"),Call("IsHermitian",A),All(X,Vec,
            Implies(Seq(Delta,Sp,Neq,Sp,D(0)),b)))))
        : OverIndex(All(A,Mat,All(X,Vec,Implies(And(Call("IsHermitian",A),
            Seq(Delta,Sp,Neq,Sp,D(0))),b))),false);
    private static Formula Inertia()
    {
        var h = V("h"); var k = V("k");
        Formula P(Formula z) => Call("posIndex",z);
        Formula N(Formula z) => Call("negIndex",z);
        Formula Z(Formula z) => Call("zeroIndex",z);
        Formula AddOne(Formula z) => Seq(z,Sp,Plus,Sp,D(1));
        var positive = Implies(Lt(D(0),Delta), And(Equal(P(h),AddOne(P(k))),
            And(Equal(N(k),N(h)),Equal(Z(k),AddOne(Z(h))))));
        var negative = Implies(Lt(Delta,D(0)), And(Equal(P(k),P(h)),
            And(Equal(N(h),AddOne(N(k))),Equal(Z(k),AddOne(Z(h))))));
        return Assumptions(Some(k,Call("IsHermitian",M),And(positive,negative)));
    }
}
