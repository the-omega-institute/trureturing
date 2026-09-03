using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GoldenCriticalSpectrum;

internal sealed class EulerPronyArithmeticRealizationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/GoldenCriticalSpectrum/EulerPronyArithmeticRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Von Mangoldt Euler data generate exact finite Prony traces. The meromorphically "
            + "continued logarithmic derivative then maps each stored zeta-zero pole to a "
            + "golden Prony node with its multiplicity-derived residue weight.",
        H("Euler Data to Arithmetic Prony Nodes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("euler-mellin-node-is-the-standard-character"),
                DeclarationHandle.Create(Prefix + "euler_mellin_prony_node_eq_cpow"),
                H("Golden Euler nodes equal standard Mellin characters"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive integer address, the golden exponential of its normalized logarithmic coordinate is exactly the complex power n raised to minus the Mellin step.")),
                    Paragraph(Text(
                        "At unit step this specializes to the reciprocal integer node, while prime-power weights specialize through the canonical von Mangoldt formula."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-von-mangoldt-shifts-are-prony-traces"),
                DeclarationHandle.Create(Prefix + "finite_euler_shift_trace_eq_prony"),
                H("Finite von Mangoldt shift windows are exact Prony traces"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Sampling a finite von Mangoldt Dirichlet window along an arithmetic progression in the Mellin parameter factors into fixed base weights and powers of fixed Euler nodes.")),
                    Paragraph(Text(
                        "The right-hand side uses the repository's frozen crystal-time readout, so this bridge introduces no duplicate moment or delay-coordinate API."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-euler-trace-is-the-standard-dirichlet-window"),
                DeclarationHandle.Create(
                    Prefix + "finite_euler_shift_trace_eq_vonMangoldt_dirichlet_window"),
                H("The Prony trace is the finite von Mangoldt Dirichlet window"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive addresses, the same finite trace is written directly with the standard arithmetic terms Lambda(n) times n raised to the shifted negative Mellin parameter.")),
                    Paragraph(Text(
                        "This identifies the formal Prony nodes with genuine Euler characters rather than free spectral parameters."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continued-euler-trace-agrees-on-the-euler-half-plane"),
                DeclarationHandle.Create(
                    Prefix + "continued_euler_trace_eq_single_address_heat_trace"),
                H("The continued Euler trace agrees with the von Mangoldt series"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On real part greater than one, the negative logarithmic derivative of zeta is exactly the repository's von Mangoldt L-series.")),
                    Paragraph(Text(
                        "The logarithmic derivative supplies the canonical continuation used to locate the zero-side pole centers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continued-euler-trace-principal-part"),
                DeclarationHandle.Create(Prefix + "continued_euler_trace_principal_part"),
                H("Zeta multiplicity becomes the Euler-pole residue"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The analytic-unit factorization of a multiplicity-m zeta zero gives the punctured-neighborhood principal part minus m divided by s minus rho.")),
                    Paragraph(Text(
                        "The regular remainder is the logarithmic derivative of the analytic unit. Thus the pole center and residue weight are both arithmetic data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-data-euler-pole-golden-prony-realization"),
                DeclarationHandle.Create(
                    Prefix + "zero_data_euler_pole_golden_prony_realization"),
                H("Every stored Euler pole yields an actual golden Prony node"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each canonical ZeroData entry carries a continued-Euler principal part, a nonzero golden exponential node, and a multiplicity-derived residue weight.")),
                    Paragraph(Text(
                        "Stored reflection inverts the node, and unit radius is equivalent to that zero lying on the critical line."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-zero-pole-prony-window-observability"),
                DeclarationHandle.Create(
                    Prefix + "finite_zeta_pole_prony_window_injective"),
                H("Separated zero-pole nodes have exact finite observability"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite family of distinct continued-Euler pole nodes is exactly observable from the first matching number of Prony moments through the frozen Vandermonde theorem.")),
                    Paragraph(Text(
                        "Node injectivity remains an explicit premise because one exponential sampling period can alias vertically separated frequencies."))),
                DescribeRole.Theorem))));
}
