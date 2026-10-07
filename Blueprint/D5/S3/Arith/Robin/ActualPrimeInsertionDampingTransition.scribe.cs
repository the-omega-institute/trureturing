using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualPrimeInsertionDampingTransitionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adding the actual prime 3 at a fixed common clock produces exactly one damping sign transition in the full compensated Laplace integral.",
        H("Actual Prime Insertion and Damping"),
        Blocks(
            Paragraph(Text(
                "For z=2 and z=3, let E_z(s) be the product of 1-p^(-s) over the actual primes p<=z. "
                + "Both normalized ratios are evaluated at s=1+v/log(3). Their linear compensation is "
                + "the exact derivative at v=0, namely the sum of log(p)/(p-1), divided by log(3). "
                + "Let J_z(sigma) be the integral on the whole positive half-axis of "
                + "exp(-sigma*v) times this compensated numerator, divided by v^2.")),
            Describe.Lean(
                DescribeId.Create("actual-prime-insertion-damping-transition"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/ActualPrimeInsertionDampingTransition.result"),
                H("A unique positive damping threshold for the actual complete integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every sigma>0, both literal compensated integrands are absolutely integrable. "
                        + "There exists sigma_star>0 for which J_3(sigma_star)-J_2(sigma_star)=0. "
                        + "The difference is strictly negative for every 0<sigma<sigma_star and strictly "
                        + "positive for every sigma>sigma_star. These strict signs imply uniqueness.")),
                    Paragraph(Text(
                        "Writing c=log(2)/log(3), the exact difference has density "
                        + "h(v)=((2-exp(-c*v))*(1-exp(-v))-v)/(2*v^2). "
                        + "A curvature factor proves that its numerator has one positive crossing r. "
                        + "The tilted integral exp(sigma*r)*(J_3(sigma)-J_2(sigma)) is strictly increasing. "
                        + "Taylor expansion and dominated convergence give a positive high-damping limit "
                        + "for sigma times the difference. A logarithmic estimate with a nonpositive "
                        + "entire remaining tail gives a negative low-damping witness.")),
                    Paragraph(Text(
                        "The common clock is essential: evaluating the z=2 product at its own log(2) "
                        + "clock would change this assertion. This result controls the first compensated "
                        + "Laplace term for the actual insertion {2} to {2,3}. The other two factorial-density "
                        + "terms, the complete Robin residual, and RH remain unresolved."))),
                DescribeRole.Theorem))));
}
