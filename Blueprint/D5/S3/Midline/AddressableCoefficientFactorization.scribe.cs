using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class AddressableCoefficientFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-axis zeta coefficients split pointwise into public half-density, phase, and scaling factors.",
        H("Addressable Coefficient Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("addressable-coefficient-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/AddressableCoefficientFactorization.addressable_coefficient_factorization"),
                H("Every addressable coefficient has the three-factor decomposition"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, DeltaLower, Comma, F.Id("t"), InMacro,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    Forall, Sp, F.Id("a"), InMacro,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("labeledZetaCoefficient")), Open,
                    Frac, Grp(D(1)), Grp(D(2)), Plus, DeltaLower, Plus,
                    F.Id("i"), F.Id("t"), Comma, F.Id("a"), Close, Eq,
                    Operatorname, Grp(F.Id("labeledZetaCoefficient")), Open,
                    Frac, Grp(D(1)), Grp(D(2)), Comma, F.Id("a"), Close,
                    Sp, Cdot, Sp,
                    Operatorname, Grp(F.Id("verticalPhase")), Open,
                    F.Id("t"), Comma, F.Id("a"), Close,
                    Sp, Cdot, Sp,
                    Operatorname, Grp(F.Id("horizontalWeight")), Open,
                    DeltaLower, Comma, F.Id("a"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For arbitrary real delta and t and every PrimeAxisTable address a, "
                        + "the concrete coefficient at (1/2 + delta) + it is the product of "
                        + "the coefficient at 1/2, the existing verticalPhase at t, and the "
                        + "existing horizontalWeight at delta. No sign or nonzero hypothesis "
                        + "is needed for this coefficient identity.")),
                    Paragraph(Text(
                        "The proof unfolds only the public labeledZetaCoefficient, verticalPhase, "
                        + "and horizontalWeight declarations. Positivity of primeAxisEncoding "
                        + "supplies the nonzero base needed to apply Complex.cpow_add twice. It "
                        + "does not invoke the private additive helper inside SpectralDynamics, "
                        + "so this theorem is independently addressable from the public API.")),
                    Paragraph(Text(
                        "Repository search found OffLineCoefficientScaling.off_line_coefficient_scaling_spec, "
                        + "which factors the generic exponential family labeledZeta and bundles "
                        + "scaling-ledger consequences. It is related but not the concrete "
                        + "prime-axis labeledZetaCoefficient statement using the public phase and "
                        + "weight factors. Pinned Mathlib search found Complex.cpow_add, which is "
                        + "reused directly. The equality is term-wise at one address and asserts "
                        + "nothing about a coefficient sum or analytic continuation."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Weil/SpectralDynamics"))]));
}
