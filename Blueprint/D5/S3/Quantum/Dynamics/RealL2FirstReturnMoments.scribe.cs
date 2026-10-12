using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class RealL2FirstReturnMomentsDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Dynamics/RealL2FirstReturnMoments.endpoint_moments";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete real half-line and its finite path have identical endpoint moments "
            + "before the first boundary return.",
        H("Real Half-Line First Return Moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("real-l2-first-return-moments"),
            DeclarationHandle.Create(Declaration),
            H("The first boundary return contributes exactly one"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let H be the complete real Hilbert space of square-summable sequences "
                        + "on the positive integers. Its unilateral shift satisfies S e_j = e_(j+1), "
                        + "and K_infinity = 3I-S-S*. Natural coordinate j represents source "
                        + "coordinate j+1. For n at least one, A_n is the n-point path adjacency "
                        + "matrix, K_n = 3I_n-A_n, and b_n is its first coordinate vector. "
                        + "The finite matrix acts on the Euclidean space of n real coordinates. "
                        + "For every natural k, define S_k^(n) to be the real Euclidean inner "
                        + "product of b_n with K_n^k b_n, and S_k^(infinity) to be the real "
                        + "Hilbert inner product of e_1 with K_infinity^k e_1 in H.")),
                Paragraph(Text(
                    "Write J_n for extension by zero into H. For k less than n, "
                        + "K_infinity^k e_1 = J_n K_n^k b_n. At order n the infinite iterate "
                        + "has the additional coordinate (-1)^n e_(n+1). "
                        + "Self-adjointness splits an endpoint moment into a pairing of two "
                        + "iterates. Below order 2n at least one factor has not reached the "
                        + "boundary; at order 2n the new coordinate is paired with itself "
                        + "and contributes one."))),
            DescribeRole.Theorem))));

    private static Formula Moment(string kind, Formula k) =>
        Seq(F.Id("S"), Underscore, Grp(k), Caret, Grp(kind == "infinity" ? Infty : F.Id(kind)));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula twoN = Seq(D(2), n);
        return Disp(Seq(
            Forall, Sp, n, Sp, InMacro, Sp, nat, Comma, Sp,
            D(1), Sp, Leq, Sp, n, Sp, Rightarrow, Sp,
            Open, Forall, Sp, k, Sp, InMacro, Sp, nat, Comma, Sp,
            k, Sp, Lt, Sp, twoN, Sp, Rightarrow, Sp,
            Moment("n", k), Sp, Eq, Sp, Moment("infinity", k), Close,
            Sp, Land, Sp,
            Moment("infinity", twoN), Sp, Minus, Sp, Moment("n", twoN),
            Sp, Eq, Sp, D(1), Dot));
    }
}
