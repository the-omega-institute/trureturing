using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class FiniteSynthesisGramDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/FiniteSynthesisGramDistance.";
    private static Formula V => F.Id("V");
    private static Formula X => F.Id("x");
    private static Formula G => F.Id("G");
    private static Formula B => F.Id("b");
    private static Formula P => Seq(F.Id("P"), Underscore, Grp(F.Id("S")));
    private static Formula MP => Seq(Operatorname, Grp(F.Id("MP")), Open, G, Close);
    private static Formula Inverse => Seq(G, Caret, Grp(Minus, D(1)));
    private static Formula NormSq(Formula a) => Seq(Vert, Sp, a, Vert, Caret, Grp(D(2)));
    private static Formula Inner(Formula a, Formula b) =>
        Seq(Langle, Sp, a, Comma, Sp, b, Rangle);
    private static Formula DistanceSq => Seq(Operatorname, Grp(F.Id("infDist")),
        Open, X, Comma, F.Id("S"), Close, Caret, Grp(D(2)));
    private static Formula BindV => Seq(Forall, Sp, V, Colon, F.Id("E"), To,
        Underscore, Grp(F.Id("k")), F.Id("H"), Comma, Sp);
    private static Formula BindVX => Seq(BindV, Forall, Sp, X, InMacro, Sp, F.Id("H"), Comma, Sp);
    private static DocumentBlock Display(Formula formula) => Paragraph(Math(Disp(formula)));
    private static Formula Sub(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula C => F.Id("c");
    private static Formula J => F.Id("j");
    private static Formula Iota => F.Iota;
    private static Formula Coeff => Pow(Seq(Mathbb, Grp(F.Id("C"))), Iota);
    private static Formula SumC => Seq(Sum, Underscore, Grp(J, InMacro, Iota), Sub(C, J));
    private static Formula XRef => Sub(X, Sub(F.Id("i"), D(0)));
    private static Formula Q => F.Id("q");
    private static Formula TStar => Sub(F.Id("t"), Star);
    private static Formula CStar => Sub(C, Star);
    private static Formula Energy(Formula c) => Inner(c, Seq(G, c));
    private static Formula SumStar => Seq(Sum, Underscore, Grp(J, InMacro, Iota),
        Sub(Seq(Open, CStar, Close), J));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite synthesis into a Hilbert space gives a singular Gram formula for projection and distance.",
        H("Finite Synthesis Gram Distance"),
        Blocks(
            Paragraph(Text(
                "Universally, k is an RCLike field, E is a finite-dimensional inner-product "
                + "space, and H is a complete inner-product space over k. Every V below is "
                + "continuous and k-linear. Set S = range V, G = V* V and b = V* x. "
                + "P denotes the independently defined orthogonal projection onto S, "
                + "infDist is the metric infimum over S, and MP is the constructed "
                + "Moore-Penrose inverse. No injectivity or invertibility is assumed.")),
            Describe.Lean(
                DescribeId.Create("finite-synthesis-gram-projection"),
                DeclarationHandle.Create(Prefix + "finite_synthesis_gram_projection"),
                H("Operator projection identity"),
                StatementSource.FromAuthor(Disp(Seq(BindV, P, Sp, Eq, Sp,
                    V, MP, V, Caret, Grp(Star)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The adjoint target lies in the Gram range. The first Penrose law "
                    + "then yields the normal equation, and the residual is orthogonal "
                    + "to the entire synthesis range. Projection uniqueness gives the "
                    + "displayed equality of operators on H."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-synthesis-gram-distance"),
                DeclarationHandle.Create(Prefix + "finite_synthesis_gram_distance"),
                H("Squared infimum distance"),
                StatementSource.FromAuthor(Disp(Seq(BindVX, DistanceSq, Sp, Eq, Sp,
                    NormSq(X), Minus, Re, Open, Inner(B, Seq(MP, B)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Projection minimality identifies infDist with the residual norm; "
                    + "the squared-norm expansion gives the Gram quadratic expression."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-synthesis-gram-quadratic-real"),
                DeclarationHandle.Create(Prefix + "finite_synthesis_gram_quadratic"),
                H("Reality of the quadratic expression"),
                StatementSource.FromAuthor(Disp(Seq(BindVX,
                    Inner(B, Seq(MP, B)), Sp, Eq, Sp, NormSq(Seq(P, X))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nonnegative real squared norm on the right is coerced into k. "
                    + "Thus over the complex field this proves reality as well as the value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-moore-penrose-ordinary-inverse"),
                DeclarationHandle.Create(Prefix + "moore_penrose_eq_inverse"),
                H("Identification with the ordinary inverse"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("A"), Colon,
                    F.Id("E"), Equiv, Underscore, Grp(F.Id("k")), F.Id("E"), Comma, Sp,
                    Operatorname, Grp(F.Id("MP")), Open, F.Id("A"), Close, Sp, Eq, Sp,
                    F.Id("A"), Caret, Grp(Minus, D(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A is any linear equivalence on E. Its ordinary inverse satisfies "
                    + "all four laws, so the imported uniqueness theorem applies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-synthesis-gram-distance-inverse"),
                DeclarationHandle.Create(Prefix + "finite_synthesis_gram_distance_inverse"),
                H("Invertible Gram specialization"),
                StatementSource.FromAuthor(Disp(Seq(BindVX, Forall, Sp,
                    G, Colon, F.Id("E"), Equiv, Underscore, Grp(F.Id("k")), F.Id("E"),
                    Comma, Sp, G, Sp, Eq, Sp, V, Caret, Grp(Star), V, Sp, Rightarrow, Sp,
                    DistanceSq, Sp, Eq, Sp, NormSq(X), Minus,
                    Re, Open, Inner(B, Seq(Inverse, B)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Only this specialization assumes that the Gram operator is a linear "
                    + "equivalence. The singular case remains covered by the preceding identities."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application: a fixed coherent affine constraint.")),
            Paragraph(Text(
                "Let ι be any finite nonempty index set, let i₀ be one of its elements, "
                + "and let H be a finite-dimensional complex Hilbert space. Thus the number "
                + "of amplitudes is at least one. For any actual family x : ι → H, retain "
                + "its fixed cross-input complex phases. Give the coefficient space C^ι "
                + "its usual Euclidean inner product, conjugate-linear in the first slot. "
                + "The following application uses the actual synthesis and its Gram operator:")),
            Display(Seq(F.Id("X"), C, Eq, Sum, Underscore, Grp(J, InMacro, Sp, Iota),
                Sub(C, J), Sub(X, J), Comma, Sp,
                G, Eq, Pow(F.Id("X"), Star), F.Id("X"), Comma, Sp,
                B, Eq, Seq(Mathbf, Grp(D(1))))),
            Display(Seq(F.Id("D"), Eq, Op("span"), Underscore, Grp(Seq(Mathbb, Grp(F.Id("C")))),
                OpenBrace, Sub(X, J), Minus, XRef, Colon, J, InMacro, Sp, Iota, CloseBrace,
                Comma, Sp, Q, Eq, Sub(F.Id("P"), Pow(F.Id("D"), Perp)), XRef,
                Comma, Sp, TStar, Eq, NormSq(Q))),
            Paragraph(Text(
                "Every coefficient vector c has Gram energy equal to the real squared "
                + "norm of its synthesis. Since b has every coordinate equal to one, "
                + "the constraint is exactly sum c_j = 1, without conjugating the "
                + "coefficients or changing the input phases.")),
            Display(Seq(Forall, Sp, C, InMacro, Sp, Coeff, Comma, Sp,
                Energy(C), Eq, NormSq(Seq(F.Id("X"), C)), Comma, Sp,
                Inner(B, C), Eq, SumC)),
            Display(Seq(Forall, Sp, F.Id("z"), InMacro, Sp, F.Id("H"), Comma, Sp,
                Open, Exists, Sp, C, InMacro, Sp, Coeff, Comma, Sp,
                SumC, Eq, D(1), Land, Sp, F.Id("X"), C, Eq, F.Id("z"), Close,
                Leftrightarrow, Sp, F.Id("z"), Minus, XRef, InMacro, Sp, F.Id("D"))),
            Paragraph(Text(
                "For the forward affine-image inclusion, subtract x_i₀ and distribute "
                + "the coefficient sum. For the reverse inclusion, write z − x_i₀ as "
                + "a linear combination of x_j − x_i₀, then add 1 minus the sum of those "
                + "coefficients to the i₀ coordinate. This gives actual feasible "
                + "coefficients. Projection gives q − x_i₀ in D and q orthogonal to D. "
                + "Consequently q is feasible and the minimum is attained:")),
            Display(Seq(Min, Underscore, Grp(C, InMacro, Sp, Coeff, Comma, SumC, Eq, D(1)),
                Energy(C), Eq, TStar, Eq, NormSq(Q))),
            Display(Seq(Exists, Sp, CStar, InMacro, Sp, Coeff, Comma, Sp,
                SumStar, Eq, D(1), Land, Sp, F.Id("X"), CStar, Eq, Q, Land,
                Energy(CStar), Eq, TStar)),
            Display(Seq(Forall, Sp, C, InMacro, Sp, Coeff, Comma, Sp,
                SumC, Eq, D(1), Rightarrow, Sp,
                NormSq(Seq(F.Id("X"), C)), Eq, NormSq(Q), Plus,
                NormSq(Seq(F.Id("X"), C, Minus, Q)), Ge, Sp, TStar)),
            Paragraph(Text("Range case, including singular Gram operators.")),
            Paragraph(Text(
                "Take G⁺ to be the constructed Moore-Penrose inverse, not an assumed "
                + "optimization oracle. Suppose b lies in range G and put p = G⁺b. "
                + "The first Penrose law gives Gp = b. Hence a = ⟨b,p⟩ is the real "
                + "number ‖Xp‖². It is strictly positive: Xp = 0 would imply Gp = 0 "
                + "and then b = 0, impossible for a nonempty coefficient set.")),
            Display(Seq(B, InMacro, Sp, Op("range"), G, Rightarrow, Sp,
                F.Id("p"), Eq, Pow(G, Plus), B, Comma, Sp,
                G, F.Id("p"), Eq, B, Comma, Sp,
                F.Id("a"), Eq, Inner(B, F.Id("p")), Eq,
                NormSq(Seq(F.Id("X"), F.Id("p"))), Gt, D(0))),
            Display(Seq(CStar, Eq, Pow(F.Id("a"), Seq(Minus, D(1))), F.Id("p"),
                Comma, Sp, SumStar, Eq, D(1), Comma, Sp,
                Energy(CStar), Eq, TStar, Eq, Pow(F.Id("a"), Seq(Minus, D(1))))),
            Paragraph(Text(
                "For any feasible c, the normal equation makes Xc_* orthogonal to "
                + "X(c − c_*). The squared-norm decomposition proves minimality, "
                + "so this explicit normalized Moore-Penrose vector attains the same "
                + "minimum as q. No invertibility of G is used.")),
            Paragraph(Text("Nonrange case and an actual kernel minimizer.")),
            Paragraph(Text(
                "If b does not lie in range G, the identities range G = (ker G)⊥ "
                + "and ker G = ker X supply a kernel vector k whose inner product "
                + "with b is nonzero. Normalize that vector by this inner product:")),
            Display(Seq(Neg, Open, B, InMacro, Sp, Op("range"), G, Close, Rightarrow, Sp,
                Exists, Sp, F.Id("k"), InMacro, Sp, Ker, Sp, G, Comma, Sp,
                Inner(B, F.Id("k")), Neq, D(0))),
            Display(Seq(CStar, Eq, Frac, Grp(D(1)), Grp(Inner(B, F.Id("k"))), F.Id("k"),
                Comma, Sp, SumStar, Eq, D(1), Comma, Sp,
                G, CStar, Eq, D(0), Comma, Sp,
                F.Id("X"), CStar, Eq, D(0), Comma, Sp,
                Energy(CStar), Eq, TStar, Eq, D(0))),
            Paragraph(Text(
                "This produces an actual feasible minimizer even at the singular "
                + "boundary. In the range case the value is (b*G⁺b)⁻¹ with a strictly "
                + "positive real denominator; in the nonrange case it is zero.")),
            Paragraph(Text("Interpretation and realization boundary.")),
            Paragraph(Text(
                "For a common-output task, the same linear contraction must act on "
                + "every input, and the common output includes all records in that "
                + "branch. Its coherent budget compares t |sum c_j|² with ‖Xc‖² "
                + "for every complex c; restricting to sum c_j = 1 gives the "
                + "optimizer above. The algebra does not replace a fixed-phase "
                + "amplitude family by its rays or discard input-dependent records. "
                + "It supplies an abstract optimum and coefficients, not a native "
                + "finite gate word, coherent control, or availability of the exact "
                + "projection as a physical branch.")),
            Paragraph(Text(
                "The application uses the finite Moore-Penrose construction and "
                + "Penrose laws from FiniteMoorePenroseInverse, the Gram and projection "
                + "identities above, and the standard range/kernel, span and "
                + "orthogonal-decomposition identities in Mathlib. Its source "
                + "application is the finite common-branch Gram optimum in "
                + "AURIC_SHARED_CONTENT_COMPATIBILITY_QUANTUM_ADDRESSING_AND_MAXIMAL_COMMON_BRANCH_V81. "
                + "The constrained formula is an application of these results.")))));
}
