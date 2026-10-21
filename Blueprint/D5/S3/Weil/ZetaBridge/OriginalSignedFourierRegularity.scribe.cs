using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class OriginalSignedFourierRegularityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both jumps of the literal zero extension remain present. Each boundary strip has energy h/L, and the overlap energy is retained separately in the exact norm identity. The square-root h majorant is a line L2 statement, not a global line H1 assertion. The singular Gamma-density/form-domain and strong mixed-tail assembly remain separate.",
        H("Original Signed Fourier Regularity"),
        Blocks(
                Paragraph(Text("Both jumps of the literal zero extension remain present. Each boundary strip has energy h/L, and the overlap energy is retained separately in the exact norm identity. The square-root h majorant is a line L2 statement, not a global line H1 assertion. The singular Gamma-density/form-domain and strong mixed-tail assembly remain separate.")),
                Describe.Lean(DescribeId.Create("line-mode"),
                    DeclarationHandle.Create(Owner + "lineMode"), H("lineMode"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("This is the original Ioc zero extension of the normalized profile, evaluated as a line function."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("translation-energy-definition"),
                    DeclarationHandle.Create(Owner + "translationSquaredNorm"), H("translationSquaredNorm"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The literal squared L2 displacement is the integral on the real line of the squared norm of F_n(x)-F_n(x-h)."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("boundary-strip-energies"),
                    DeclarationHandle.Create(Owner + "boundary_strip_energies"), H("boundary strip energies"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For 0<=h<=L the left strip (-L/2,-L/2+h] and the right strip (L/2,L/2+h] each contribute exactly h/L. Neither boundary jump is discarded."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("translation-squared-norm"),
                    DeclarationHandle.Create(Owner + "translation_squared_norm"), H("translation squared norm"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For 0<=h<=L the squared gap is 2*h/L+2*(1-h/L)*(1-cos(w_n*h)). The literal line integral is partitioned into the left strip, overlap and right strip. Both endpoint-strip equalities contribute h/L; the overlap norm expansion uses the conjugate-first correlation, including n=0, h=0 and h=L."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("translation-squared-norm-le"),
                    DeclarationHandle.Create(Owner + "translation_squared_norm_le"), H("translation squared norm le"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The exact gap is at most 2*h/L+w_n squared*h squared. The linear term remains for the zero mode."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("displaced-mode"),
                    DeclarationHandle.Create(Owner + "displacedMode"), H("displacedMode"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("A line L2 representative is constructed from proved MemLp of the literal zero extension and its measure-preserving translate."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("displaced-head"),
                    DeclarationHandle.Create(Owner + "displacedHead"), H("displacedHead"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The finite complex combination is formed on line L2 using every signed retained mode."))), DescribeRole.Definition),
                Describe.Lean(DescribeId.Create("finite-head-translation-bound"),
                    DeclarationHandle.Create(Owner + "finite_head_translation_bound"), H("finite head translation bound"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Minkowski on the literal zero-extended finite-head displacement gives its line L2 seminorm bound sqrt(2/L)*sum(norm(v_n))*sqrt(h)+sum(norm(v_n)*abs(w_n))*h for 0<=h<=L. The all-real-h displacedHead_ae bridge then transfers this estimate to the existing L2 class norm."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("finite-head-translation-bound-l2"),
                    DeclarationHandle.Create(Owner + "finite_head_translation_bound_l2"), H("finite head translation bound l2"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("Finite Cauchy--Schwarz gives [sqrt(2*card(S)/L)*sqrt(h)+sqrt(sum(w_n squared))*h]*sqrt(sum(norm(v_n) squared)). Empty sets and all signed zero modes are included."))), DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("displaced-head-ae"),
                    DeclarationHandle.Create(Owner + "displacedHead_ae"), H("displacedHead ae"),
                    StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The constructed finite L2 sum agrees almost everywhere with the displacement of the actual original zero-extended finite complex profile, rather than a periodic profile. This all-real-h equality transfers the literal-function L2 estimate into finite_head_translation_bound; the quantitative range remains 0<=h<=L."))), DescribeRole.Theorem))));
}
