using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class ActualPreparedSolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/ActualPreparedSolution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal prepared datum generates a real full-lattice mild path on the original interval, with unrestricted mild uniqueness, explicit beta stability, all spatial grades and smooth physical velocity.",
        H("Actual Prepared Solution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prepared-mild-solution"),
                DeclarationHandle.Create(Prefix + "prepared_mild_solution"),
                H("Prepared full-lattice mild path and its spatial grades"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For positive viscosity nu and A, nonnegative B, and real alpha and beta with absolute values at most A and B, use R equal to twice the square root of 2 A squared plus 9 B squared and tau equal to nu divided by 16384 R squared. The initial weighted coefficients are (0, alpha) at both (1,0) and (-1,0), and (3 beta/2, 3 beta/2) at both (-1,1) and (1,-1), with all other coefficients zero. Decoding these coefficients and summing their characters gives exactly the first two components of the existing real preparation. The constructed evolution uses every integer-pair frequency.")),
                    Paragraph(Text("There exists a continuous weighted Hilbert path u on the entire closed interval, equal to this datum at zero and bounded by R. Every value has zero spatial mean, conjugate coefficients at opposite frequencies, and is fixed by the Leray projection. A continuous selected Bochner Duhamel path D vanishes at zero, has norm at most R/4 on the interval, and has exactly the full row-tensor integral coefficients. The same u satisfies the heat-orbit-minus-D equation. The proof constructs the closed real carrier, proves its preservation by the actual tensor integral, and applies the contraction on the original path space with image bound 3 R/4 and contraction constant 1/2. One proof-local continuous bilinear tensor map, one row map, and one clamped selected Bochner map supply the tensor and difference calculations. Coordinate uniqueness and interval-integral linearity identify the difference of selected paths with the selected tensor difference. Every continuous full-Hilbert-space mild competitor with the same prepared initial coefficients agrees with this path throughout the interval, with no radius restriction. The proof cancels the common past in the actual coordinate integrals and restarts on finitely many short intervals. Against any radius-R prepared mild path with the same alpha and a second beta, the pointwise Hilbert distance is at most six times the absolute beta difference; the exact initial difference norm is three times that difference.")),
                    Paragraph(Text("For every natural spatial grade there is a continuous weighted Hilbert path of the same unweighted coefficients. Bounded linear and bilinear operators have the exact diffusion and nonlinear Fourier symbols, and these grade paths satisfy the strong derivative equation within the full original closed interval, including its endpoints. The diagonal agreement with the regularity theorem follows from the absolutely convergent change of variable p to k-p; that theorem contracts its first input and outputs its second. Each grade path has every time derivative within the closed interval. The actual real Fourier synthesis is jointly smooth in time and the two physical coordinates on the full closed interval, its character series is absolutely convergent at every time and position, and its physical Euclidean norm is bounded pointwise by 4 R.")),
                    Paragraph(Text("The statement does not prove the original normalized physical L2 formulation and sharp F bounds, the exact zero-mean pressure and unprojected equation, pressure smoothness, maximal smooth existence and physical velocity L-infinity continuation, or the same-time torus scaling with viscosity nu divided by (2 pi) squared. Those clauses of Recovery25.3 and Recovery25.4 remain open. The native Reg realization, bridge, variation, sensitivity and dependence proofs are retained. Source-bound registration remains unfinished: the complete candidate predicate requires an admitted source selection and reconstruction bridge. The native evidence does not supply that source binding."))),
                DescribeRole.Theorem))));
}
