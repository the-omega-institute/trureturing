using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class ActualPureQubitCostInfimumDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/ActualPureQubitCostInfimum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full finite affine-readout pure-qubit cost infimum has quadratic coefficient "
        + "one quarter of the weighted score-square projection residual.",
        H("Actual pure-qubit cost infimum"),
        Blocks(
            Describe.Lean(DescribeId.Create("spectral-sld-information"),
                DeclarationHandle.Create(Module + "spectralQFI"), H("Spectral SLD information"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In an eigenbasis of the positive semidefinite state, sum twice the squared "
                    + "modulus of each derivative entry divided by the sum of the corresponding "
                    + "eigenvalues. Terms with zero denominator are zero. Positivity on a "
                    + "two-sided neighborhood forces the derivative's kernel-to-kernel block to vanish "
                    + "(Pker D Pker = 0)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("guarded-real-infimum"),
                DeclarationHandle.Create(Module + "guardedInfimum"), H("Guarded real infimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Real infimum with explicit nonempty and bounded-below guard."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("canonical-density-bridge"),
                DeclarationHandle.Create(Module + "densityBridge"), H("Canonical density-state bridge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every positive semidefinite trace-one matrix is constructed as a canonical "
                    + "density state, with exact equality of the recovered matrix."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-program-class"),
                DeclarationHandle.Create(Module + "IsProgram"), H("Full actual program class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A fixed finite POVM and a continuously differentiable pure state curve are "
                    + "defined on an open connected interval containing the closed radius interval. "
                    + "Born probabilities are exactly affine and positive throughout. The cost is "
                    + "the actual spectral SLD information at zero. No readout rank, score sign, "
                    + "canonical arc, or zero-score effect shape is imposed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-cost-set"),
                DeclarationHandle.Create(Module + "costs"), H("Attainable actual costs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The set ranges over all actual programs in the preceding class."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-cost-infimum"),
                DeclarationHandle.Create(Module + "C2"), H("Cost infimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real infimum is used only in the branch with nonempty and lower-bounded "
                    + "cost set. Both conditions hold at every sufficiently small positive radius."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bloch"),
                DeclarationHandle.Create(Module + "bloch"), H("Bloch vector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three real Bloch coordinates of a two by two matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blochmatrix"),
                DeclarationHandle.Create(Module + "blochMatrix"), H("Bloch matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Hermitian matrix with a specified real trace and Bloch vector."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("effectreadout"),
                DeclarationHandle.Create(Module + "effectReadout"), H("Visible readout map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The linear part of the finite measurement readout sends a Bloch vector to its pairings with the effect vectors."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reframe"),
                DeclarationHandle.Create(Module + "reframe"), H("Orthogonal change of Bloch coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An orthogonal change of the Bloch vector preserves the trace coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("blochlinear"),
                DeclarationHandle.Create(Module + "blochLinear"), H("Linear Bloch map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Bloch coordinates form a real linear map on complex matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reframelinear"),
                DeclarationHandle.Create(Module + "reframeLinear"), H("Linear change of matrix coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fixed orthogonal Bloch frame induces a real linear map on matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("root"),
                DeclarationHandle.Create(Module + "root"), H("Small quadratic root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rationalized small root gives the lower diagonal effect coefficient, including zero individual scores."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("radiusmap"),
                DeclarationHandle.Create(Module + "radiusMap"), H("Radius map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The radius includes a strict margin inside the pure-state arc and is locally inverted near zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("extendedcost"),
                DeclarationHandle.Create(Module + "extendedCost"), H("Extended family cost"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cost formula extends through the zero transverse parameter for the normalization branch."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("upperdiag"),
                DeclarationHandle.Create(Module + "upperDiag"), H("Upper diagonal coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complementary quadratic root determines the upper diagonal effect coefficient."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("effect"),
                DeclarationHandle.Create(Module + "effect"), H("Actual effect matrix"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two diagonal coefficients and the normalized direction determine each effect matrix."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("arc"),
                DeclarationHandle.Create(Module + "arc"), H("Pure-state arc"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Bloch curve has one affine coordinate, one square-root coordinate, and one constant coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-rank-two-parameters"),
                DeclarationHandle.Create(Module + "actual_rank_two_parameters"), H("Actual rank-two arc and feasible coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual rank-two affine readout of a pure curve admits a fixed orthonormal frame. The invisible coordinate has constant sign on the connected open interval. The effect coefficients satisfy positivity, normalization, and the exact affine-readout relations; the visible coordinate satisfies the strict radius bound.")))),
            Describe.Lean(DescribeId.Create("actual-effect-family"),
                DeclarationHandle.Create(Module + "actual_effect_family"), H("Normalized positive effect family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any normalized centered direction, the quadratic small roots admit a differentiable normalization branch and a local inverse radius map. Along the same family the actual effects are positive semidefinite and sum to the identity, the strict arc and probability margins hold, and the extended cost has the required moment limit.")))),
            Describe.Lean(DescribeId.Create("actual-upper-family"),
                DeclarationHandle.Create(Module + "actual_upper_family"), H("Matching family of actual programs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive finite probabilities and a centered direction of unit weighted second moment, the radius family gives actual POVMs and pure curves. Their spectral cost excess has the stated moment coefficient. Scaling the direction in the infimum theorem gives the original affine data.")))),
            Describe.Lean(DescribeId.Create("actual-fisher"),
                DeclarationHandle.Create(Module + "actual_fisher"), H("Measurement Fisher lower bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every differentiable positive curve with the exact affine measurement probabilities has spectral SLD information at least the classical Fisher information. Two-sided positivity first forces the derivative's kernel-to-kernel block to vanish (Pker D Pker = 0), producing an SLD without invertibility. Positive residual squares then give the measurement bound.")))),
            Describe.Lean(DescribeId.Create("actual-rank-alternative"),
                DeclarationHandle.Create(Module + "actual_rank_alternative"), H("Rank alternative and binary cost gap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual nonconstant pure-qubit readout has rank two or incurs the binary-measurement lower bound from any negative and positive score. Rank zero and rank three are excluded by the visible projection geometry.")))),
            Describe.Lean(DescribeId.Create("actual-qubit-infimum-expansion"),
                DeclarationHandle.Create(Module + "result"), H("Exact quadratic infimum coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary finite positive probability data, a nonzero centered direction, "
                    + "and at least three distinct scores, the residual is positive and the normalized "
                    + "infimum excess tends to one quarter of that residual as real positive radii "
                    + "tend to zero. Repeated and zero individual scores are allowed. Cubic approximate "
                    + "minimizers suffice; no optimum is assumed attained. This result makes no "
                    + "two-score attainment or unrestricted CPTP processor equivalence claim.")),
                    Paragraph(Text(
                        "The lower bound uses the joint limit of feasible rank-two coefficients: "
                        + "positivity, normalization, and the spectral cost equation exclude a positive "
                        + "limiting transverse parameter when three scores are distinct. The remaining "
                        + "diagonal coefficients converge to the normalized weighted score squares. "
                        + "An exact matching inequality then gives the quadratic lower coefficient. "
                        + "The rank-one branch has a fixed positive cost gap, and a smooth family "
                        + "of actual programs supplies the matching upper bound.")))))));
}
