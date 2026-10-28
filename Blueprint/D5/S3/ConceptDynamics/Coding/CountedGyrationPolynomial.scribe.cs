using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedGyrationPolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binomial polynomial and explicit integral numerator",
        H("The binomial polynomial and explicit integral numerator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("countedgyrationpolynomial-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedGyrationPolynomial.rationalGyrationPolynomial_eval_signed"),
                H("One polynomial at every signed integer tuple"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The polynomial has one variable for each R or S matrix entry. For every vertex word and rank pattern its term is the same integer forward weight multiplied by the product of binomial polynomials. The polynomial choose(X,k) is the falling factorial divided by k!. The existing Ring.choose identities evaluate it integrally at every signed integer, including negative entries and the empty product.")),
                    Paragraph(Text("Consequently evaluation equals signedGyrationLift at all integer tuples. At natural tuples the same lift is orderTypeGyrationLift, already proved to represent the actual relative forward gyration modulo d. Residues are taken through this integer lift. There is no ring homomorphism from all rationals to ZMod d and none is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedgyrationpolynomial-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedGyrationPolynomial.integralGyrationNumerator_map"),
                H("Clear the denominator by the actual occurrence bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Each rank width is at most the number of occurrences of its entry. Summing all occurrence counts gives exactly 2d. The existing multinomial factorial divisibility theorem proves that the product of the width factorials divides the factorial of their sum, hence divides (2d)!. The numerator is explicit: multiply each integral falling-factorial product by its integer forward weight and the natural quotient (2d)! divided by the product of width factorials.")),
                    Paragraph(Text("Under coefficient inclusion into the rationals, this numerator is exactly (2d)! times rationalGyrationPolynomial. Its evaluation at every signed integer tuple is (2d)! times signedGyrationLift. This is a polynomial identity with a divisibility proof, not a finite interpolation check or a numerical inference.")),
                    Paragraph(Text("The method uses classical binomial bases for integer-valued polynomials and multinomial factorial divisibility. No novelty, optimal denominator, full SGCC, or assertion about physical realizations is made. Negative tuples belong to the algebraic extension; actual counted graphs use natural entries."))),
                DescribeRole.Theorem))));
}
