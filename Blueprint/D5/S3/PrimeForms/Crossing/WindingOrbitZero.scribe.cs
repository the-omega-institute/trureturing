using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class WindingOrbitZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact crossing-sandwich propagation gives a unique zero on every admissible "
            + "forward orbit with nonnegative even initial winding phase.",
        H("Unique Winding Zero on a Crossing Orbit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("crossing-sandwich-transformation"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/WindingOrbitZero.crossingSandwich"),
                H("The crossing sandwich transformation"),
                StatementSource.FromAuthor(SandwichFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The self-map S sends a positive-coordinate matrix A to M A M, where "
                        + "M = [[3,1],[2,1]] is the fixed determinant-one crossing matrix."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("crossing-orbit-has-unique-winding-zero"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/WindingOrbitZero."
                    + "sandwich_orbit_has_unique_winding_zero"),
                H("An even winding phase reaches zero exactly once"),
                StatementSource.FromAuthor(UniqueZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A = [[a,b],[c,d]] have positive a, c, and d and determinant one. "
                            + "If its winding phase is the nonnegative even integer 2k, then "
                            + "the forward crossing-sandwich orbit has winding phase zero at "
                            + "exactly one natural time, namely k.")),
                    Paragraph(Text(
                        "The imported exact propagation laws show that right and left "
                            + "multiplication by M lower the winding phase by two in total. "
                            + "Direct determinant arithmetic proves that positivity and the "
                            + "determinant-one relation survive every sandwich.")),
                    Paragraph(Text(
                        "Mathlib's Function.Semiconj.iterate_right transports both the matrix "
                            + "orbit and the phase law through arbitrary iteration. The resulting "
                            + "closed form Psi(S^n(A)) = Psi(A)-2n makes existence and uniqueness "
                            + "a rational-arithmetic consequence.")),
                    Paragraph(Text(
                        "This closes only the E.37 clause that exact stepwise descent yields the "
                            + "forward-orbit formula and a unique zero for an even nonnegative "
                            + "initial phase. It does not formalize the source's lattice-orbit "
                            + "classification, its all-integer two-sided orbit claim, or the "
                            + "m=36 genealogy.")),
                    Paragraph(Text(
                        "Repository search found and reused the exact one-step Rademacher phase "
                            + "laws in ExactPropagation. Pinned-Mathlib searches found the exact "
                            + "iteration transport theorem Function.Semiconj.iterate_right but no "
                            + "matching constant-step unique-zero theorem."))),
                DescribeRole.Theorem))));

    private static Formula SandwichFormula() => Disp(Seq(
        F.Id("S"), Open, F.Id("A"), Close, Eq,
        F.Id("M"), F.Id("A"), F.Id("M"), Comma, Quad, Sp,
        F.Id("M"), Eq, Begin, Grp(F.Id("pmatrix")),
        D(3), Amp, D(1), RowBreak, D(2), Amp, D(1), End, Grp(F.Id("pmatrix"))));

    private static Formula UniqueZeroFormula()
    {
        Formula phase = Seq(Operatorname, Grp(F.Id("Psi")));
        return Disp(Seq(
            Forall, Sp, F.Id("A"), Eq,
            Begin, Grp(F.Id("pmatrix")),
            F.Id("a"), Amp, F.Id("b"), RowBreak,
            F.Id("c"), Amp, F.Id("d"), End, Grp(F.Id("pmatrix")), Comma, Sp,
            F.Id("k"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
            D(0), Lt, F.Id("a"), Sp, Land, Sp,
            D(0), Lt, F.Id("c"), Sp, Land, Sp,
            D(0), Lt, F.Id("d"), Sp, Land, Sp,
            F.Id("a"), F.Id("d"), Eq, F.Id("b"), F.Id("c"), Plus, D(1), Sp, Land, Sp,
            phase, Open, F.Id("A"), Close, Eq, D(2), F.Id("k"), Sp,
            Rightarrow, Sp, Exists, Bang, Sp, F.Id("n"), InMacro,
            Mathbb, Grp(F.Id("N")), Comma, Esc,
            phase, Open, F.Id("S"), Caret, Grp(F.Id("n")),
            Open, F.Id("A"), Close, Close, Eq, D(0), Dot));
    }
}
