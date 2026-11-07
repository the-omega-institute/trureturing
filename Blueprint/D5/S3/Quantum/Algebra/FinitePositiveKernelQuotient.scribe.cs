using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class FinitePositiveKernelQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite positive semidefinite complex matrix defines a complete quotient with its prescribed Gram matrix.",
        H("Finite Positive Kernel Quotients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-quotient-inner-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/FinitePositiveKernelQuotient.inner_mk"),
                H("The quotient inner product"),
                StatementSource.FromAuthor(InnerFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let M be any finite type and let D be a Hermitian positive semidefinite complex matrix on M. " +
                    "Space(D,hD) is the algebraic complex vector-space quotient of the functions M to Complex " +
                    "by the kernel of matrix multiplication by D. The map mk sends a coefficient vector to its class. " +
                    "The inner product of the classes of c and d is star(c) dot (D times d), with star acting " +
                    "coordinatewise. Thus changing representatives by elements of the matrix kernel leaves the value unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-positive-kernel-quotient"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/FinitePositiveKernelQuotient.finite_positive_kernel_quotient"),
                H("Dimension, spanning labels and unique unitary equivalence"),
                StatementSource.FromAuthor(RealizationFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite M, every positive semidefinite D on M, and every proof hD of this property, " +
                        "the space H=Space(D,hD) has the displayed inner product, complex dimension rank(D), " +
                        "and labelled vectors v(i)=mk(D,hD,e(i)). Here e(i) is one in coordinate i and zero elsewhere. " +
                        "Their pairwise inner products are D(i,j), and their complex linear span is all of H. " +
                        "The installed norm and inner product make H a finite-dimensional complete inner product space. " +
                        "Zero and singular matrices are included; M may be empty.")),
                    Paragraph(Text(
                        "Let E be any complete complex inner product space, with no dimension assumption on E. " +
                        "If w:M to E has Gram matrix D and spans E, there is exactly one complex linear isometric " +
                        "equivalence U:H to E such that U(v(i))=w(i) for every i. A complex linear isometric " +
                        "equivalence is the unitary equivalence meant here. The spanning hypothesis determines U uniquely.")),
                    Paragraph(Text(
                        "The positive matrix gives the coefficient space its pre-inner product through " +
                        "Matrix.toInnerProductSpace. Matrix.PosSemidef.dotProduct_mulVec_zero_iff identifies " +
                        "the zero-length vectors with the kernel of D. The first isomorphism theorem therefore " +
                        "identifies the algebraic matrix-kernel quotient with the separation quotient. " +
                        "Transporting the separation quotient inner product gives the formula above. " +
                        "The quotient dimension is the dimension of the range of D; finite dimension gives completeness.")),
                    Paragraph(Text(
                        "For a spanning family w, the analysis map x to the function i maps to inner(w(i),x) " +
                        "is injective. Each coordinate is continuous, so this makes E a scalar-valued reproducing " +
                        "kernel Hilbert space. Its kernel function at i applied to z is z times w(i). " +
                        "Equal Gram matrices give equal reproducing kernels. RKHS.equiv and RKHS.equiv_kerFun " +
                        "then give the labelled isometry, and agreement on the spanning labels proves uniqueness.")),
                    Paragraph(Text(
                        "The statements here concern a single positive matrix and its spanning realizations. " +
                        "They do not assert a direct-sum or tensor-product identification of two such quotient spaces."))),
                DescribeRole.Theorem))));

    private static Formula InnerFormula()
    {
        Formula m = F.Id("M"), d = F.Id("D"), h = F.Id("hD"), c = F.Id("c"), e = F.Id("d");
        return Disp(Seq(
            Forall, Sp, m, Colon, F.Id("FiniteType"), Comma, Esc,
            Forall, Sp, d, Colon, Call("Matrix", m, m, F.Id("Complex")), Comma, Esc,
            Forall, Sp, h, Colon, Call("PosSemidef", d), Comma, Esc,
            Forall, Sp, c, Comma, e, Colon, Call("Coefficients", m, F.Id("Complex")), Comma, Esc,
            Call("inner", Call("mk", d, h, c), Call("mk", d, h, e)), Sp, Eq, Sp,
            Call("dotProduct", Call("star", c), Call("mulVec", d, e))));
    }

    private static Formula RealizationFormula()
    {
        Formula m = F.Id("M"), d = F.Id("D"), h = F.Id("hD"), i = F.Id("i"), j = F.Id("j");
        Formula space = Call("Space", d, h), label = Call("label", d, h);
        Formula e = F.Id("E"), w = F.Id("w"), u = F.Id("U"), t = F.Id("V");
        Formula maps(Formula f) => Seq(Forall, Sp, i, Colon, m, Comma, Sp,
            Call("apply", f, Call("apply", label, i)), Sp, Eq, Sp, Call("w", i));
        return Disp(Seq(
            Forall, Sp, m, Colon, F.Id("FiniteType"), Comma, Esc,
            Forall, Sp, d, Colon, Call("Matrix", m, m, F.Id("Complex")), Comma, Esc,
            Forall, Sp, h, Colon, Call("PosSemidef", d), Comma, Esc,
            Open, Forall, Sp, F.Id("c"), Comma, F.Id("d"), Colon,
                Call("Coefficients", m, F.Id("Complex")), Comma, Esc,
                Call("inner", Call("mk", d, h, F.Id("c")), Call("mk", d, h, F.Id("d"))),
                Eq, Call("dotProduct", Call("star", F.Id("c")), Call("mulVec", d, F.Id("d"))), Close,
            Sp, Land, Esc,
            Call("finrank", F.Id("Complex"), space), Eq, Call("rank", d), Sp, Land, Esc,
            Open, Forall, Sp, i, Comma, j, Colon, m, Comma, Sp,
                Call("inner", Call("apply", label, i), Call("apply", label, j)), Eq, Call("D", i, j), Close,
            Sp, Land, Esc,
            Call("span", F.Id("Complex"), Call("range", label)), Eq, F.Id("top"), Sp, Land, Esc,
            Forall, Sp, e, Colon, F.Id("CompleteComplexInnerProductSpace"), Comma, Esc,
            Forall, Sp, w, Colon, m, To, e, Comma, Esc,
            Open, Forall, Sp, i, Comma, j, Colon, m, Comma, Sp,
                Call("inner", Call("w", i), Call("w", j)), Eq, Call("D", i, j), Close,
            Sp, Implies, Esc,
            Call("span", F.Id("Complex"), Call("range", w)), Eq, F.Id("top"), Sp, Implies, Esc,
            Exists, Sp, u, Colon, Call("LinearIsometryEquiv", F.Id("Complex"), space, e), Comma, Esc,
            Open, maps(u), Close, Sp, Land, Esc,
            Open, Forall, Sp, t, Colon, Call("LinearIsometryEquiv", F.Id("Complex"), space, e), Comma, Esc,
                Open, maps(t), Close, Sp, Implies, Sp, t, Eq, u, Close));
    }

    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
}
