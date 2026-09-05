using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class LinearObjectiveDualDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/LinearObjectiveDual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational primal and dual witnesses certify finite linear objective bounds and endpoint optimality.",
        H("Exact Rational Linear Objective Certificates"),
        Blocks(
            Paragraph(Text(
                "A feasible point satisfies a finite rational system A x less than or equal to b. A linear query is evaluated by an exact finite rational sum.")),
            Paragraph(Text(
                "An upper certificate is a nonnegative combination of constraint rows that represents the objective coefficients and whose weighted right-hand side is below the proposed upper value. A lower certificate applies the same construction to the negated objective.")),
            Paragraph(Text(
                "Weak duality proves universal validity. A feasible primal point with the same objective value upgrades validity to exact endpoint optimality. External optimization software may propose both witnesses, while Lean checks every coefficient, sign, sum, and equality.")),
            Describe.Lean(
                DescribeId.Create("upper-bound-of-certificate"),
                DeclarationHandle.Create(Prefix + "upper_bound_of_certificate"),
                H("A rational upper dual certificate proves a universal bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every feasible primal point, the nonnegative weighted constraint sum equals the objective and is bounded by the certificate right-hand side."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-bound-of-certificate"),
                DeclarationHandle.Create(Prefix + "lower_bound_of_certificate"),
                H("A rational lower dual certificate proves a universal bound"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The certificate represents the negated objective, so exact weak duality yields the claimed lower bound after reversing the sign."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-lower-bound-of-certificate-and-witness"),
                DeclarationHandle.Create(
                    Prefix + "exact_lower_bound_of_certificate_and_witness"),
                H("Matching rational dual and primal witnesses certify an exact lower endpoint"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The dual witness supplies universal validity and the primal witness supplies attainment at the same exact rational value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-upper-bound-of-certificate-and-witness"),
                DeclarationHandle.Create(
                    Prefix + "exact_upper_bound_of_certificate_and_witness"),
                H("Matching rational dual and primal witnesses certify an exact upper endpoint"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem packages the proof obligation required for certified linear-program endpoint sharpness."))),
                DescribeRole.Theorem))));
}
