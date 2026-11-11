using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class UniformThetaShellErrorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact supremum over the real theta-error shell.",
        H("Exact supremum over the real theta-error shell"),
        Blocks(
            Paragraph(Text("SOURCE ONLY: UNCOMPILED_UNACCEPTED. No Lean elaboration, kernel/axiom closure, native report, Scribe compilation, official acceptance, or four-slot Reg validation was run. Full Lean bodies are candidate proof attempts. The ordinary Pro derivation and the independent ordinary audit are fallible inputs, not axioms; this context already includes the repository and prior source candidates. No sterile-context or model-diversity claim is made. Native checking may expose elaboration or proof gaps. Root owns both pre-existing native queues and later integration.")),
            Paragraph(Text("shellError(X) is the sSup of the exact image {|theta(y)-y| : y is real and X/2<=y<=2X}. The source proves nonemptiness, boundedness using monotonicity and nonnegativity of the existing theta, domination of each actual real shell point, and the supremum upper-bound rule. Existing coarse prime_number_limits supplies one all-real tail for theta(y)/y; a threshold 2Y controls the entire shell and gives shellError(X)/X tending to zero. The source also treats real, including negative, exponents in a global conditional theta law by bounding logarithms of ratios. It never replaces the supremum by a postulated envelope.")),
            Paragraph(Text("Owning Lean source SHA256: febebddb21eaa9510e56ed0ee12967e3949781dd8514cc381eafa3fa3d5569c7. The complete new-declaration signatures, source line locations, import closure and dependency patches are exposed in source-manifest.json and dependency-boundary.json.")),
            Paragraph(Text("Four-slot Reg is not supplied. Missing evidence after the compiled telescope is an actual full-law variation/realization for this literal prime-power inventory, an exact specialization/control witness on its valid arithmetic domain, the corresponding realization/equivalence proofs, and the residual/open-slot statement accepted by the current Reg contract. Abstract invented spectra, weakened prime support or assumed final inequalities would not be faithful. Root must attach that precise missing-evidence statement to its existing issue workflow after native compilation; no issue or fake declared_validated status is created in this source-only packet.")),
            Describe.Lean(
                DescribeId.Create("uniformthetashellerror-errorvalues-nonempty"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.errorValues_nonempty"),
                H("errorValues nonempty"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem errorValues_nonempty {X : ℝ} (hX : 0 ≤ X) : (errorValues X).Nonempty"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniformthetashellerror-errorvalues-bddabove"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.errorValues_bddAbove"),
                H("errorValues bddAbove"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem errorValues_bddAbove {X : ℝ} (hX : 0 ≤ X) : BddAbove (errorValues X)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniformthetashellerror-pointwise-le-shellerror"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.pointwise_le_shellError"),
                H("pointwise le shellError"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem pointwise_le_shellError {X y : ℝ} (hX : 0 ≤ X)\n    (hy : y ∈ Set.Icc (X / 2) (2 * X)) : |Chebyshev.theta y - y| ≤ shellError X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniformthetashellerror-shellerror-nonneg"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_nonneg"),
                H("shellError nonneg"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem shellError_nonneg {X : ℝ} (hX : 0 ≤ X) : 0 ≤ shellError X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniformthetashellerror-shellerror-le"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_le"),
                H("shellError le"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem shellError_le {X A : ℝ} (hX : 0 ≤ X)\n    (hA : ∀ y : ℝ, y ∈ Set.Icc (X / 2) (2 * X) → |Chebyshev.theta y - y| ≤ A) :\n    shellError X ≤ A"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniformthetashellerror-shellerror-eventually-le-mul"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_eventually_le_mul"),
                H("shellError eventually le mul"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem shellError_eventually_le_mul {ε : ℝ} (hε : 0 < ε) :\n    ∀ᶠ X : ℝ in atTop, 0 < X ∧ shellError X ≤ ε * X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniformthetashellerror-shellerror-ratio-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_ratio_tendsto_zero"),
                H("shellError ratio tendsto zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem shellError_ratio_tendsto_zero :\n    Tendsto (fun X : ℝ => shellError X / X) atTop (𝓝 0)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniformthetashellerror-shell-rpow-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shell_rpow_bound"),
                H("shell rpow bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem shell_rpow_bound {X y : ℝ} (hX : 0 < X)\n    (hy : y ∈ Set.Icc (X / 2) (2 * X)) (a : ℝ) :\n    y ^ a ≤ (2 : ℝ) ^ |a| * X ^ a"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniformthetashellerror-shellerror-global-power"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/UniformThetaShellError.shellError_global_power"),
                H("shellError global power"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean statement:\ntheorem shellError_global_power {σ B K Y : ℝ} (hK : 0 ≤ K)\n    (hglobal : ∀ y : ℝ, Y ≤ y → 0 < y → 0 < log y →\n      |Chebyshev.theta y - y| ≤ K * y ^ σ * (log y) ^ B) :\n    ∀ X : ℝ, max 4 (2 * Y) < X →\n      shellError X ≤ (K * (2 : ℝ) ^ |σ| * (2 : ℝ) ^ |B|) *\n        X ^ σ * (log X) ^ B"))),
                DescribeRole.Theorem)
        )));
}
