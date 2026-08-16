using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class ThirdOrderIntegralityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational K-conjugate of an integer matrix is integral exactly on one mod-three class.",
        H("The Third-Order Integrality Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("third-order-k-conjugate-integrality-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/ThirdOrderIntegrality.k_conjugate_integral_iff"),
                H("K-conjugation is integral exactly on one congruence class"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, GammaLower, Sp, InMacro, Sp,
                    F.Id("M"), Underscore, D(2), Open, Mathbb, Grp(F.Id("Z")), Close,
                    Comma, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, F.Id("j"), Comma, Sp,
                    D(3), Sp, Mid, Sp,
                    Open, F.Id("K"), GammaLower, Operatorname, Grp(F.Id("adj")), Sp,
                    F.Id("K"), Close, Underscore, Grp(F.Id("ij")), Close,
                    Sp, Iff, Sp,
                    D(3), Sp, Mid, Sp, Open,
                    GammaLower, Underscore, Grp(D(0, 0)), Plus,
                    D(2), GammaLower, Underscore, Grp(D(0, 1)), Plus,
                    GammaLower, Underscore, Grp(D(1, 0)), Plus,
                    D(2), GammaLower, Underscore, Grp(D(1, 1)), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K = [[1,-2],[2,-1]], whose determinant is 3. For an integer 2x2 "
                        + "matrix gamma, the adjugate formula writes the rational inverse of K as "
                        + "one third of adj(K). Thus K*gamma*adj(K) is the numerator of the rational "
                        + "conjugate K*gamma*K^{-1}, and that conjugate has integer entries exactly "
                        + "when all four numerator entries are divisible by 3.")),
                    Paragraph(Text(
                        "Expanding those four entries modulo 3 gives respectively the negative or "
                        + "positive of the single linear form g00 + 2*g01 + g10 + 2*g11. Hence all "
                        + "four divisibility conditions are equivalent to one congruence. The Lean "
                        + "proof reads the forward implication from entry (0,0), constructs a quotient "
                        + "for each entry in the reverse implication, and reuses the preceding module's K.")),
                    Paragraph(Text(
                        "Repository search found no equivalent D5 declaration. Pinned-mathlib and "
                        + "Loogle searches found Matrix.adjugate_fin_two and Matrix.inv_def as the exact "
                        + "library support, but no theorem for this specific K-congruence. This closes "
                        + "only clause (i), the K-integrality characterization, of residual E.73. It "
                        + "does not claim K-normalization, conjugacy with Gamma_0(3), the (2,6,infinity) "
                        + "group identification, or the later crossing-class corollary."))),
                DescribeRole.Theorem
            )),
        []));
}
