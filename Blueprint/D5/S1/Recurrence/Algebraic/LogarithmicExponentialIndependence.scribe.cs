using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class LogarithmicExponentialIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic independence of a logarithmic exponential series and its derivative.",
        H("Algebraic Independence of a Formal Logarithm"),
        Blocks(
            Paragraph(Text("Let E=exp(X) in the ring of rational formal power series, and let "
                + "F=-log(2-E), normalized by F(0)=0. Equivalently, F is the unique series "
                + "with zero constant coefficient and derivative E/(2-E). "
                + "The denominator has constant coefficient one and is therefore invertible.")),
            Describe.Lean(
                DescribeId.Create("logarithmic-exponential-mobius-transcendence"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Algebraic/LogarithmicExponentialIndependence.mobius_transcendental"),
                H("A rational change of variable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a field extension of characteristic zero, "
                    + "put g=e/(2-e). Transcendence ensures 2-e is nonzero, and "
                    + "(1+g)(2-e)=2 ensures 1+g is nonzero. The inverse formula "
                    + "e=2g/(1+g) shows that an algebraic g would make e algebraic."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("logarithmic-exponential-transcendence-tower"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Algebraic/LogarithmicExponentialIndependence.rational_primitive_independent"),
                H("Independence in a tower of fields"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume compatible algebra maps in the four-field "
                    + "tower, characteristic zero for H_0, x in K_0 transcendental over Q_0, "
                    + "e in H_0 transcendental over K_0, and f in L transcendental over H_0. "
                    + "The preceding rational change preserves the middle transcendence. "
                    + "Two applications of the independence theorem for a tower give "
                    + "the three coordinates in L, in the order x,f,e/(2-e)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("logarithmic-exponential-algebraic-independence"),
                DeclarationHandle.Create(
                    "D5/S1/Recurrence/Algebraic/LogarithmicExponentialIndependence.algebraically_independent"),
                H("Three algebraically independent series"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every polynomial P in three indeterminates with "
                        + "rational coefficients, evaluating its indeterminates at X,F,F' "
                        + "gives zero only when P itself is zero. There is no bound on "
                        + "the degree, support, or size of the coefficients of P.")),
                    Paragraph(Text("First, the variable X and the exponential E are "
                        + "algebraically independent. Under formal differentiation, "
                        + "each polynomial multiple p(X)E^j lies in the generalized "
                        + "eigenspace with eigenvalue j. Repeated application of D-j "
                        + "differentiates p until it vanishes. Distinct generalized "
                        + "eigenspaces are independent, so a finite sum of these "
                        + "polynomial multiples can vanish only term by term.")),
                    Paragraph(Text("Next consider the rational differential field Q(t,u) "
                        + "with derivative of t equal to one and derivative of u equal "
                        + "to u. The function u/(2-u) has no rational primitive. "
                        + "For a reduced fraction p/q, the equation for a primitive "
                        + "forces q(2)=0 and p(2) nonzero. Factoring q at u=2, "
                        + "differentiating the factor, canceling its power, and "
                        + "evaluating at two gives a nonzero quantity equal to zero.")),
                    Paragraph(Text("If F were algebraic over Q(X,E), differentiate its "
                        + "monic minimal polynomial. Minimality makes the resulting "
                        + "polynomial of smaller degree vanish identically. Its next "
                        + "to leading coefficient shows that -a_(n-1)/n is a rational "
                        + "primitive of E/(2-E), contradicting the preceding obstruction. "
                        + "Thus X,E,F form a transcendence tower. Finally, replacing E "
                        + "by F'=E/(2-E) preserves transcendence because "
                        + "E=2F'/(1+F'). The conclusion concerns formal power series; "
                        + "it asserts no statement about operads or Koszulness."))),
                DescribeRole.Theorem))));
}
