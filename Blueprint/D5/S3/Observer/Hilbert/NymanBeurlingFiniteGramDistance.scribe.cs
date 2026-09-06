using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hilbert;

internal sealed class NymanBeurlingFiniteGramDistanceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance.";
    private static Formula N => F.Id("N");
    private static Formula Chi => Seq(Mathrm, Grp(F.Id("chi")));
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula CN => Seq(C, Caret, Grp(N));
    private static Formula Sub(string name, Formula i) => Seq(F.Id(name), Underscore, Grp(i));
    private static Formula V => Sub("V", N);
    private static Formula G => Sub("G", N);
    private static Formula B => Sub("b", N);
    private static Formula S => Sub("S", N);
    private static Formula DnSq => Seq(Sub("d", N), Caret, Grp(D(2)));
    private static Formula MP => Seq(Operatorname, Grp(F.Id("MP")), Open, G, Close);
    private static Formula Inner(Formula a, Formula b) =>
        Seq(Langle, Sp, a, Comma, Sp, b, Rangle);
    private static Formula BindN => Seq(Forall, Sp, N, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The source finite-stage Gram formulas hold on the actual complex Nyman-Beurling L2 carrier.",
        H("Nyman-Beurling Finite Gram Distance"),
        Blocks(
            Paragraph(Text(
                "The carrier is Lp(C, 2, volume restricted to (0,infinity)), using the "
                + "repository's canonical positiveMeasure. The target chi is the Lp class "
                + "of the indicator of (0,1). For every natural a at least one, f_a is the "
                + "complexification of the canonical real fractionalReciprocal vector; "
                + "sourceVector_coe_ae proves its representative is "
                + "x |-> ofReal(fract(1/(a*x))) almost everywhere. target_coe_ae likewise "
                + "identifies the indicator representative, and target_norm_sq proves "
                + "its squared norm is one from the measure of (0,1).")),
            Paragraph(Text(
                "For each natural N, coefficients lie in EuclideanSpace C (Fin N), "
                + "with i representing the source index a=i+1. V_N is finite synthesis, "
                + "S_N is the span of f_1 through f_N, G_N = V_N* V_N, and b_N = V_N* chi. "
                + "The distance d_N is independently defined as Metric.infDist chi S_N. "
                + "MP denotes the constructed Moore-Penrose inverse with all four Penrose "
                + "identities proved in the attributed upstream port.")),
            Describe.Lean(
                DescribeId.Create("nyman-beurling-finite-synthesis"),
                DeclarationHandle.Create(Prefix + "synthesis_apply"),
                H("Canonical finite synthesis"),
                StatementSource.FromAuthor(Disp(Seq(BindN,
                    Forall, Sp, F.Id("c"), InMacro, Sp, CN, Comma, Sp,
                    V, F.Id("c"), Sp, Eq, Sp, Sum, Underscore,
                    Grp(F.Id("i"), InMacro, Sp, Operatorname, Grp(F.Id("Fin")), Open, N, Close),
                    Sub("c", F.Id("i")), Sub("f", Seq(F.Id("i"), Plus, D(1)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The basis-defined continuous linear map has exactly the source's "
                    + "finite sum, with the one-based index represented by i+1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nyman-beurling-finite-range"),
                DeclarationHandle.Create(Prefix + "synthesis_range"),
                H("Range equals the source span"),
                StatementSource.FromAuthor(Disp(Seq(BindN,
                    Operatorname, Grp(F.Id("range")), Open, V, Close, Sp, Eq, Sp, S))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The shell is defined as the span. Its finite dimension and "
                    + "completeness are derived, so its orthogonal projection needs no "
                    + "extra closure assumption."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nyman-beurling-gram-entries"),
                DeclarationHandle.Create(Prefix + "gramOperator_entry"),
                H("Gram entries"),
                StatementSource.FromAuthor(Disp(Seq(BindN, Forall, Sp,
                    F.Id("i"), Comma, F.Id("j"), InMacro, Sp,
                    Operatorname, Grp(F.Id("Fin")), Open, N, Close, Comma, Sp,
                    Open, G, Sub("e", F.Id("j")), Close, Underscore, Grp(F.Id("i")),
                    Sp, Eq, Sp, Inner(Sub("f", Seq(F.Id("i"), Plus, D(1))),
                        Sub("f", Seq(F.Id("j"), Plus, D(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The e_j are the standard orthonormal coefficient vectors. "
                    + "These entries identify the Gram operator with the source matrix."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nyman-beurling-correlation-entries"),
                DeclarationHandle.Create(Prefix + "correlations_entry"),
                H("Target correlations"),
                StatementSource.FromAuthor(Disp(Seq(BindN, Forall, Sp,
                    F.Id("i"), InMacro, Sp, Operatorname, Grp(F.Id("Fin")),
                    Open, N, Close, Comma, Sp, Open, B, Close, Underscore, Grp(F.Id("i")),
                    Sp, Eq, Sp, Inner(Sub("f", Seq(F.Id("i"), Plus, D(1))), Chi)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inner product is conjugate-linear in its first argument, "
                    + "so this is the source's b_N = V_N* chi convention."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nyman-beurling-finite-gram-distance"),
                DeclarationHandle.Create(Prefix + "nyman_beurling_finite_gram_distance"),
                H("All three finite-stage Gram distance clauses"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")), BindN, RowBreak,
                    F.Id("P"), Underscore, Grp(S), Sp, Eq, Sp,
                    V, MP, V, Caret, Grp(Star), RowBreak,
                    Land, Sp, DnSq, Sp, Eq, Sp, D(1), Minus, Inner(B, Seq(MP, B)), RowBreak,
                    Land, Sp, Open, Forall, Sp, F.Id("A"), Colon, CN,
                    Equiv, Underscore, Grp(C), CN, Comma, Sp,
                    F.Id("A"), Sp, Eq, Sp, G, Sp, Rightarrow, Sp,
                    DnSq, Sp, Eq, Sp, D(1), Minus,
                    Inner(B, Seq(F.Id("A"), Caret, Grp(Minus, D(1)), B)), Close,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both distance equalities are in C, with the real squared distance "
                    + "coerced into C. The first therefore also proves that the Gram "
                    + "quadratic expression is real. The projection clause is an equality "
                    + "of operators on the full Lp carrier. Only the third clause assumes "
                    + "invertibility, expressed by a linear equivalence whose underlying "
                    + "map is the Gram operator. The theorem holds for every natural N, "
                    + "including zero, hence in particular every source stage N at least one. "
                    + "It asserts the finite distance formula, with no assertion about "
                    + "the limiting residual or the Riemann hypothesis."))), DescribeRole.Theorem))));
}
