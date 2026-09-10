using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilDivisorWindowCorrespondenceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/WeilDivisorWindowCorrespondence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual divisor carrier gives the canonical arithmetic Mellin window exactly up to its explicit missing-divisor function, with the complete prime-action correction retained.",
        H("Divisor Window Correspondence"),
        Blocks(
            Describe.Lean(DescribeId.Create("divisor-window"),
                DeclarationHandle.Create(Owner + "divisorWindow"),
                H("Independent synthesis over the actual divisors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use Nat.divisors, the same finite arithmetic carrier appearing in the 5040 divisor-partition research. On [-a,a], synthesize 4*exp(x/2)*sum_{d divides N} h(d*exp(x)), and extend by zero. This is a function on the original logarithmic window, not a newly named scalar partition or Fourier transform."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("missing-divisor-window"),
                DeclarationHandle.Create(Owner + "missingDivisorWindow"),
                H("Complete arithmetic defect on the visible prefix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum over every positive d<=M that does not divide N, using the same support, seed and half-density. Missing terms are combined as complex functions before taking any norms. No sign or positivity is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("divisor-window-exact-defect"),
                DeclarationHandle.Create(Owner + "divisor_window_exact_defect"),
                H("Exact function-level dictionary including the remainder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For N nonzero, exp(2a)<=M, and a complex seed vanishing above exp(a), prove divisorWindow=windowMellinSum-missingDivisorWindow at every real point. Divisors beyond M vanish by the actual seed support. The remaining finite divisor set is identified with the divisibility filter of the original prefix. Coverage is not an assumption of this theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("divisor-window-prime-action"),
                DeclarationHandle.Create(Owner + "divisor_window_prime_action"),
                H("Original prime action with the missing-divisor correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the existing prime_forward_mellin_identity to the original window, and transport the exact function-level defect through the independently defined primeForward. Retain the log-seed defect, coordinate-times-defect, and prime action on the defect. This connects divisor data to the actual Lambda(n)/sqrt(n) translations without assuming Robin positivity or suppressing missing prime powers."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("divisor-window-prefix-correspondence"),
                DeclarationHandle.Create(Owner + "divisor_window_prefix_correspondence"),
                H("Finite arithmetic coverage discharges the defect"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If every positive d<=M divides N, the actual missing-divisor set is empty, hence the two independently specified functions agree. The condition is on integer divisibility, not a supplied operator or Fourier identification."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("divisor-windows-5040-and-2520"),
                DeclarationHandle.Create(Owner + "divisor_windows_5040_and_2520"),
                H("5040 and 2520 realize the same small window"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For exp(2a)<=10 and any supported complex seed, both 5040 and 2520 realize the original window with cutoff 10. All ten divisor checks are discharged in the proof. This is a shared finite-window function, although the scalar reciprocal-divisor sums differ.")),
                    Paragraph(Text("The sharper L2 threshold exp(2a)<=11, the compressed-translation Euler product and its logarithmic derivative, and the origin-normalized genuine-ground/prolate numerical comparison are separately proved on paper in RH_RESEARCH_LANE_THEORY.md. Equality at the sharper threshold uses a null endpoint and is not claimed by the pointwise Lean theorem. Lean elaboration, Scribe emission and the transitive axiom audit have not run. No scalar Robin estimate is promoted to full Weil positivity, a spectral gap, or an unbounded-scale Xi limit."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining"))]));
}
