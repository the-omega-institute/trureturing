using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class XiGlobalGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The classical pole-removed xi function satisfies a uniform exponential bound on the complex plane.",
        H("Global Growth of the Riemann Xi Function"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("xi-reading-norm-le-exp-three-halves"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/XiGlobalGrowth.xi_reading_norm_le_exp_three_halves"),
                H("A uniform three-halves growth bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("C"), InMacro, Mathbb, Grp(F.Id("R")), Comma,
                    F.Id("C"), Gt, D(0), Land,
                    Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma,
                    Vert, Xi, Open, F.Id("s"), Close, Vert, Le,
                    Exp, Open, F.Id("C"), Open, D(1), Plus, Vert, Sp, F.Id("s"), Vert,
                    Close, Caret, Grp(Frac, Grp(D(3)), Grp(D(2))), Close))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Zeros/lagarias2007li")),
                Blocks(
                    Paragraph(Text(
                        "There is one positive real constant C such that the displayed bound holds "
                        + "for every complex s. Here xi is the classical Riemann xi function, with "
                        + "xi(0) = xi(1) = 1/2, and the exponent is the real number three halves.")),
                    Paragraph(Text(
                        "Lagarias's order-one theorem implies this weaker estimate. The proof here "
                        + "uses the symmetric theta-tail Mellin integral for the pole-removed "
                        + "completion. Continuity controls the compact initial interval, while "
                        + "exponential theta decay controls the remaining half-line. A logarithmic "
                        + "estimate bounds both complex powers uniformly in s by an integrable "
                        + "exponential majorant. Integration and the polynomial xi factor then "
                        + "give the asserted constant.")),
                    Paragraph(Text(
                        "The estimate is unconditional and includes both endpoints. It supplies "
                        + "a norm bound for subsequent complex-analytic estimates; no identity "
                        + "between Li coefficients and an infinite zero sum is asserted."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Analytic/CompletedZetaMellinReconstruction"))]));
}
