using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaTail;

internal sealed class DensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For s>1, normalized prime-selection profiles have explicit mass, logarithmic moment and binary entropy.",
        H("Prime-selection density integrals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("density"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q"),
                H("Selection density"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For s>1 and u>0, q(s,u)=a(s)^s/(a(s)^s+u^s), where a(s)=s*sin(pi/s)/pi. This is a Bernoulli inclusion probability for primes on the logarithmic spatial scale."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("range"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_range"),
                H("Interior probabilities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every s>1, the density lies strictly between zero and one on the positive half-line. Thus every nondegenerate compact interval has both selected and unselected capacity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("continuity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_continuous"),
                H("Continuous profile"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every s>1, the density is continuous on the positive half-line. Compact restrictions can therefore be approximated by finitely many bins."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mass"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_mass"),
                H("Unit mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every s>1, the density is integrable on (0,infinity) and its total integral is one. The proof applies the existing power-kernel integral to the parameter a(s)^s."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("logarithmic-moment"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_log_moment"),
                H("Logarithmic moment"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every s>1, the logarithmic moment is absolutely integrable on (0,infinity) and equals log(a(s))-(pi/s)*cos(pi/s)/sin(pi/s). A power substitution first evaluates the Mellin integral for exponents between zero and s. Differentiation at exponent one is justified by an integrable bound using two nearby Mellin exponents."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entropy"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaTail/Density.q_entropy"),
                H("Integrated binary entropy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every s>1, the binary entropy of the density is integrable on (0,infinity) and its total integral equals s-pi*cos(pi/s)/sin(pi/s). The pointwise entropy identity separates the logarithmic weight, mass and logarithmic moment. The logarithmic weight integrates to s by an improper integration by parts with vanishing endpoint terms."))),
                DescribeRole.Theorem))));
}
