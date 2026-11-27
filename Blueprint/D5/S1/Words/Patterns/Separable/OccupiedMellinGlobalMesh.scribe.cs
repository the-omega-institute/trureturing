using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns.Separable;

internal sealed class OccupiedMellinGlobalMeshDocument : IScribeDocumentDefinition
{
    private static Formula Ratio(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula x, Formula p) => Seq(x, Caret, Grp(p));
    private static Formula Abs(Formula x) => Seq(Left, Lvert, Sp, x, Right, Rvert);
    private static Formula I => F.Id("i");
    private static Formula K => F.Id("K");
    private static Formula M => F.Id("M");
    private static Formula N => F.Id("n");
    private static Formula R => F.Id("R");
    private static Formula S => F.Id("s");
    private static Formula Reals => Seq(Mathbb, Grp(R));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Domain => Seq(Open, D(0), Comma, Infty, Close);
    private static Formula ShiftedSample => Call("sample", Beta, Ratio(D(2), N), Ratio(Seq(I, Plus, D(1)), N));
    private static Formula UnshiftedSample => Call("sample", Beta, D(0), S);

    private static Formula Estimate() => Disp(Seq(
        Begin, Grp(F.Id("gathered")),
        Forall, Sp, Beta, InMacro, Sp, Reals, Comma, Sp, N, Comma, K, Comma, M,
        InMacro, Sp, Naturals, Comma, RowBreak, Grp(),
        D(0), Le, Beta, Le, Ratio(D(3), D(4)), Sp, Land, Sp,
        D(0), Lt, N, Sp, Land, Sp, D(0), Lt, K, Sp, Land, Sp,
        D(2), Cdot, Sp, N, Lt, M, Sp, Land, Sp,
        Ratio(M, N), Le, Pow(DeltaLower, Seq(Minus, D(1))), Longrightarrow, RowBreak, Grp(),
        Call("Summable", Seq(I, Mapsto, Abs(ShiftedSample))), Sp, Land, Sp,
        Call("IntegrableOn", Seq(S, Mapsto, UnshiftedSample), Domain), Sp, Land, RowBreak, Grp(),
        Abs(Seq(Int, Underscore, Grp(Domain), UnshiftedSample, Thin, F.Id("ds"), Minus,
            Ratio(D(1), N), Sum, Underscore, Grp(I, Eq, D(0)), Caret, Grp(Infty), ShiftedSample)),
        Le, RowBreak, Grp(),
        D(6, 4), Cdot, Sp, Pow(DeltaLower, Ratio(D(3), D(2))), Plus,
        D(1, 1, 2), Cdot, Sp, Pow(DeltaLower, Ratio(D(1), D(4))), Plus,
        D(1, 6), Cdot, Sp, Pow(N, Seq(Minus, Ratio(D(1), D(4)))), Plus,
        Ratio(Seq(D(3, 2), Cdot, Sp, Pow(DeltaLower, Seq(Minus, Ratio(D(1, 7), D(4))))), N), Plus,
        D(8), Cdot, Sp, Pow(R, Seq(Minus, Ratio(D(1), D(2)))),
        End, Grp(F.Id("gathered"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single estimate compares the positive half-line integral with the entire shifted positive lattice.",
        H("Global paired Mellin quadrature"),
        Blocks(Describe.Lean(
            DescribeId.Create("global-mellin-mesh-error"),
            DeclarationHandle.Create("D5/S1/Words/Patterns/Separable/OccupiedMellinGlobalMesh.global_mesh_error"),
            H("Absolute summability, integrability, and a global error bound"),
            StatementSource.FromAuthor(Estimate()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Set delta equal to K/n and R equal to (M-1)/n. Ratios and powers are real. "
                    + "The size condition forces delta below one half. All integration is with respect to Lebesgue measure on the positive half-line. "
                    + "The sample in the integral is unshifted; the mesh uses the exact shift 2/n.")),
                Paragraph(Text(
                    "The discrete blocks are the positive indices below K, the left regular block, the center block, "
                    + "the right regular block through M-1, and the tail beginning at M. The corresponding continuous "
                    + "partition stops the right regular block at M/n, not at R. The continuous tail bound is enlarged "
                    + "using R at most M/n. Each regular block compares the left samples against its integral. "
                    + "The center estimate bounds a larger block, including the right endpoint, so it bounds the "
                    + "half-open center block without counting that endpoint twice."))),
            DescribeRole.Theorem))));
}
