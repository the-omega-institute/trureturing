using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class GeneralInstrumentSurvivalLimitDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Measurement/GeneralInstrumentSurvivalLimit.survival_tendsto_maximal_fixed_effect";

    private static readonly Formula N = F.Id("N"), Hm = F.Id("H"), RhoF = F.Rho;
    private static readonly Formula A = F.Id("a"), I = F.Id("i"), Eff = F.Id("F");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The survival effects of a general no-click instrument decrease in the Loewner order to the largest "
            + "effect fixed by the dual no-click map.",
        H("Survival Effects of a General Instrument Converge to the Largest Fixed Effect"),
        Blocks(Describe.Lean(
            DescribeId.Create("general-survival-limit"),
            DeclarationHandle.Create(Declaration),
            H("Monotone limit and maximal fixed effect"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let alpha and iota be finite, let Q_a be the no-click and L_i the click Kraus operators on the "
                        + "d-dimensional space with the completeness relation, let A(X) be the sum of Q_a^* X Q_a "
                        + "over a, and let S_N = A^N(I). The order is the Loewner order: X <= Y means that Y - X "
                        + "is positive semidefinite.")),
                Paragraph(Text(
                    "The map A preserves positive semidefiniteness and hence the order, and S_0 - S_1 is the sum of "
                        + "L_i^* L_i, so the survival effects decrease and stay between 0 and I. For every vector the "
                        + "quadratic form of S_N is a bounded decreasing real sequence and converges; the "
                        + "polarization identity expresses every matrix entry through four quadratic forms, so S_N "
                        + "converges entrywise to a matrix F.")),
                Paragraph(Text(
                    "Positive semidefiniteness passes to limits, which gives 0 <= F <= S_N. Continuity of A and "
                        + "uniqueness of limits give A(F) = F. If 0 <= H <= I and A(H) = H, then H = A^N(H) <= "
                        + "A^N(I) = S_N for every N, and in the limit H <= F. The trace pairing with any rho is "
                        + "continuous, so Tr(rho S_N) converges to Tr(rho F)."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complete = Seq(
            Sum, Underscore, Grp(A, Sp, InMacro, Sp, Alpha), Sp, Sub("Q", A), Caret, Grp(Star), Sp, Sub("Q", A),
            Sp, Plus, Sp, Sum, Underscore, Grp(I, Sp, InMacro, Sp, Iota), Sp,
            Sub("L", I), Caret, Grp(Star), Sp, Sub("L", I), Sp, Eq, Sp, F.Id("I"));
        Formula chain = Seq(
            D(0), Sp, Leq, Sp, Sub("S", N), Comma, Quad, Sp,
            Sub("S", Seq(N, Plus, D(1))), Sp, Leq, Sp, Sub("S", N), Sp, Leq, Sp, F.Id("I"),
            Comma, Quad, Sp, Eff, Sp, Leq, Sp, Sub("S", N));
        Formula fixedPoint = Seq(
            D(0), Sp, Leq, Sp, Eff, Sp, Leq, Sp, F.Id("I"), Comma, Quad, Sp,
            Mathcal, Grp(F.Id("A")), Open, Eff, Close, Sp, Eq, Sp, Eff);
        Formula maximal = Seq(
            Forall, Sp, Hm, Comma, Sp, D(0), Sp, Leq, Sp, Hm, Sp, Leq, Sp, F.Id("I"), Sp, Land, Sp,
            Mathcal, Grp(F.Id("A")), Open, Hm, Close, Sp, Eq, Sp, Hm, Sp, Rightarrow, Sp, Hm, Sp, Leq, Sp, Eff);
        Formula trace = Seq(
            Forall, Sp, RhoF, Comma, Sp, Operatorname, Grp(F.Id("Tr")), Open, RhoF, Sp, Sub("S", N), Close, Sp, To,
            Sp, Operatorname, Grp(F.Id("Tr")), Open, RhoF, Sp, Eff, Close);
        return Disp(Seq(
            complete, Sp, Rightarrow, Sp, Exists, Sp, Eff, Comma, Sp, Sub("S", N), Sp, To, Sp, Eff, Comma,
            RowBreak, Grp(),
            Open, Forall, Sp, N, Comma, Sp, chain, Close, Comma, RowBreak, Grp(),
            fixedPoint, Comma, RowBreak, Grp(),
            maximal, Comma, RowBreak, Grp(),
            trace, Dot));
    }

    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
}
