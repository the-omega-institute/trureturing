using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class FibonacciObservationDocument : IScribeDocumentDefinition
{
    private const string IdentityDeclaration =
        "D5/S3/Geometry/Hyperideal/FibonacciObservation.discriminant_sq";

    private const string PhaseDeclaration =
        "D5/S3/Geometry/Hyperideal/FibonacciObservation.observe_phase_indistinguishable";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic CFMP return observation has a persistent phase congruence modulo 5k.",
        H("Persistent five-phase ambiguity in the CFMP return observation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-observation-identities"),
                DeclarationHandle.Create(IdentityDeclaration),
                H("Discriminant square and Fibonacci conjugacy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For integer pairs, D(x,y)=(-x+2y,2x+y), C(x,y)=(2x-y,x+2y), "
                            + "F(x,y)=(y,x+y), and J(x,y)=(y,x). The exact identities are "
                            + "D^2=5I, C=D followed by J, and C followed by JFJ equals "
                            + "F followed by C.")),
                    Paragraph(Text(
                        "These identities identify the cyclic CFMP return observation with "
                            + "the golden discriminant after a coordinate swap, and show that "
                            + "the Fibonacci evolution preserves its observation fibres."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-observation-phase-indistinguishability"),
                DeclarationHandle.Create(PhaseDeclaration),
                H("Persistent phase indistinguishability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write modEq_m(a,b) for m dividing b-a. For k,t in the natural "
                            + "numbers, the phase shift s(k,t)=(kt,2kt) changes the first "
                            + "observed coordinate by zero and the second by 5kt.")),
                    Paragraph(Text(
                        "Therefore every shifted pair z+s(k,t) has exactly the same two "
                            + "return observations modulo 5k. This is a finite obstruction "
                            + "to recovering framed gluing parameters from the Fibonacci "
                            + "return readout alone.")),
                    Paragraph(Text(
                        "The exact congruence kernel is characterized by "
                            + "FibonacciObservation.kernel_phase_characterization: every "
                            + "input in the 5k-kernel has the form (k*t,2*k*t+5*k*s). "
                            + "The dual image condition is "
                            + "FibonacciObservation.image_condition: 2*r+s must vanish "
                            + "modulo five.")),
                    Paragraph(Text(
                        "At the concrete modulus 5040=5*1008, the same theorem gives the "
                            + "five-part phase ambiguity is exhibited. The factor seven in 5040 does "
                            + "not enter the displayed kernel generator; no broader arithmetic "
                            + "conclusion is claimed here.")),
                    Paragraph(Text(
                        "The obstruction is scoped to the framed return-parameter observation. "
                            + "It does not claim five distinct unmarked manifolds, a general "
                            + "hyperbolic realization, or a solution of the minimum-six CFMP "
                            + "problem."))),
                DescribeRole.Theorem))));

}
