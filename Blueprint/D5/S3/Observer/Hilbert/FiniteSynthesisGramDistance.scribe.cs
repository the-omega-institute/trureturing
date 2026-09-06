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
                DescribeRole.Theorem))));
}
