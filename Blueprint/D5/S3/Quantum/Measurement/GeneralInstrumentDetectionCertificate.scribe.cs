using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class GeneralInstrumentDetectionCertificateDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/GeneralInstrumentDetectionCertificate.detection_certificate";

    private static readonly Formula N = F.Id("N"), M = F.Id("m"), G = F.Id("g"), A = F.Id("a"), I = F.Id("i");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "When a general no-click instrument has no definite dark direction, the survival effects decay "
            + "geometrically in blocks of d rounds, and the survival probabilities of every initial state have "
            + "sum at most d / g.",
        H("Uniform Detection Certificate for General Instruments"),
        Blocks(Describe.Lean(
            DescribeId.Create("general-detection-certificate"),
            DeclarationHandle.Create(Declaration),
            H("Block decay of the survival effects"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let alpha and iota be finite, let Q_a be the no-click and L_i the click Kraus operators on the "
                        + "d-dimensional space with the completeness relation, let S_N be the survival effects and D_d "
                        + "the stable dark layer; the order is the Loewner order.")),
                Paragraph(Text(
                    "If D_d is zero, then I - S_d is positive definite, so its spectrum is positive and "
                        + "compact, and some g > 0 satisfies g I <= I - S_d. For any such g, S_d <= (1 - g) I; the dual no-click map is positive, "
                        + "monotone and homogeneous, so S_{(m+1)d} = A^d(S_{md}) <= (1 - g)^m A^d(I) = (1 - g)^m S_d "
                        + "<= (1 - g)^{m+1} I.")),
                Paragraph(Text(
                    "For a density matrix rho, the real parts of the traces Tr(rho S_N) are nonnegative and decrease in N; the "
                        + "block of d consecutive terms starting at md is at most d (1 - g)^m, and the geometric "
                        + "sum of these block bounds is at most d / g."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complete = Seq(
            Sum, Underscore, Grp(A, Sp, InMacro, Sp, Alpha), Sp, Sub("Q", A), Caret, Grp(Star), Sp, Sub("Q", A),
            Sp, Plus, Sp, Sum, Underscore, Grp(I, Sp, InMacro, Sp, Iota), Sp,
            Sub("L", I), Caret, Grp(Star), Sp, Sub("L", I), Sp, Eq, Sp, F.Id("I"));
        Formula bound = Seq(G, Sp, F.Id("I"), Sp, Leq, Sp, F.Id("I"), Minus, Sub("S", F.Id("d")));
        Formula decay = Seq(
            Forall, Sp, M, Comma, Sp, Sub("S", Seq(M, Sp, F.Id("d"))), Sp, Leq, Sp,
            Open, D(1), Minus, G, Close, Caret, Grp(M), Sp, F.Id("I"));
        Formula summable = Seq(
            Forall, Sp, F.Rho, Sp, Geq, Sp, D(0), Sp, F.Text, Grp(Sp, F.Id("with"), Sp),
            Operatorname, Grp(F.Id("Tr")), Sp, F.Rho, Sp, Eq, Sp, D(1), Comma, Sp,
            Open, N, Sp, Mapsto, Sp, ReTr(Sub("S", N)), Close, Sp, F.Text, Grp(Sp, F.Id("summable"), Sp), Land, Sp,
            Sum, Underscore, Grp(N), Sp, ReTr(Sub("S", N)), Sp, Leq, Sp, Frac, Grp(F.Id("d")), Grp(G));
        return Disp(Seq(
            complete, Sp, Rightarrow, RowBreak, Grp(),
            Open, Sub("D", F.Id("d")), Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp, Exists, Sp, G, Sp, Gt, Sp, D(0),
            Comma, Sp, bound, Close, Sp, Land, RowBreak, Grp(),
            Forall, Sp, G, Sp, Gt, Sp, D(0), Comma, Sp, bound, Sp, Rightarrow, Sp, Open, decay, Close, Sp, Land,
            RowBreak,
            Grp(), summable, Dot));
    }

    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));

    private static Formula ReTr(Formula x) =>
        Seq(Operatorname, Grp(F.Id("Re")), Sp, Operatorname, Grp(F.Id("Tr")), Open, F.Rho, Sp, x, Close);
}
