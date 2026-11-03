using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Resolvent;

internal sealed class ActualXiDictionaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete actual xi, reflection-folded spectrum, Taylor-moment and finite real-polynomial Hankel dictionary.",
        H("The Complete Actual Xi Dictionary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-xi-dictionary"),
                DeclarationHandle.Create("D5/S3/Zeros/Resolvent/ActualXiDictionary.actual_xi_dictionary"),
                H("All actual zeros and every Taylor and Hankel order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Dictionary keeps the independently defined original xiOdd(w) = "
                        + "(i logDeriv xiReading(1/2-iw) - firstLiMass w)/(w squared + 1/4). "
                        + "Its spectral index is the positive-height subtype of the original canonical "
                        + "distinct-zero enumeration, with all actual analytic multiplicities. "
                        + "Positive height chooses exactly one representative of each reflection pair. "
                        + "The node is minus one divided by (rho minus one half) squared, and its weight "
                        + "is twice the actual multiplicity times the normalized rho(1-rho) reciprocal times the node.")),
                    Paragraph(Text(
                        "The full record proves distinct nonzero nodes of norm less than one, nonzero "
                        + "weights, nonzero denominators, absolute weight summability, and finite node "
                        + "cuts away from zero. Reflection after conjugation restricts to an involution "
                        + "that conjugates nodes and weights and preserves multiplicity. A node is real "
                        + "exactly when the original zero is on the critical line; then node and weight "
                        + "are positive. Each off-line four-element zero orbit has precisely its two "
                        + "positive-height representatives, mapped injectively to one nonreal conjugate node pair. "
                        + "Multiplicity changes weights without duplicating the pair.")),
                    Paragraph(Text(
                        "On norm(w) less than one quarter the original xi expression is analytic and "
                        + "equals the complete folded resolvent and the normally convergent odd series. "
                        + "The moment of every order j equals the original function derivative of order "
                        + "2j+1 at zero divided by its factorial; every moment is real and all even derivatives "
                        + "vanish. W is the complete absolute weight mass and Lambda the actual supremum "
                        + "of node norms with zero included, with Lambda at most one. On every closed disk "
                        + "of radius r less than one quarter the bound is W r/(1-Lambda r squared), "
                        + "and the remainder after index J is bounded by W r (Lambda r squared) to power "
                        + "J+1 divided by the same denominator.")),
                    Paragraph(Text(
                        "For every finite real coefficient vector u and natural shift m, the Hankel form "
                        + "built from the actual derivative coefficients at indices 2m+a+b equals the real "
                        + "part of the full sum of weight times [node to power m times p(node)] squared. "
                        + "This is the complex square, not a modulus square. Only an explicit Mathlib "
                        + "RiemannHypothesis premise gives nonnegativity. The dictionary proves no unconditional "
                        + "positivity, RH, physical-space moment condition, or negative-index formula. "
                        + "The folded pair count and the full odd/even Taylor-chain count remain distinct. "
                        + "The square-source, normalized-resolvent and actual endpoint-mass suppliers are "
                        + "reused in their canonical owners. No ordinary mathematical originality is claimed.")))))));
}
