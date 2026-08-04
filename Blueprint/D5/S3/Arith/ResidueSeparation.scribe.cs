using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class ResidueSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/ResidueSeparation",
            "A modulus above both operands makes the modular reading separate distinct naturals."),
        H("Separation of Distinct Naturals by a Sufficiently Large Modular Reading"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-modulus-above-both-operands-separates-distinct-residues"),
                H("A modulus above both operands separates distinct residues"),
                LeanTheorem(
                    "D5/S3/Arith/ResidueSeparation.residue_separation"),
                LatexStatement.Create(
                    @"$$\forall m,n,M\in\mathbb{N},\ m \neq n \land \max(m,n) < M \Rightarrow "
                    + @"(m \operatorname{mod} M) \neq (n \operatorname{mod} M)$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The modular reading of a natural number at a modulus M is its remainder on "
                        + "division by M, and the theorem asks when this reading distinguishes two "
                        + "operands. It fixes natural numbers m and n that are genuinely distinct and a "
                        + "modulus M lying strictly above both, expressed as the single hypothesis that the "
                        + "larger of m and n is still smaller than M, and concludes that the two readings "
                        + "differ. The hypotheses are not vacuous: the inequality on the maximum is a real "
                        + "constraint relating the modulus to both operands at once, and the distinctness of "
                        + "m and n is the genuine premise the separation converts into distinctness of the "
                        + "readings. Strictness is essential rather than cosmetic, for a modulus equal to the "
                        + "larger operand would wrap that operand down to a smaller residue and could collapse "
                        + "the two readings together.")),
                    Paragraph(Text(
                        "The proof reads the hypothesis on the maximum as the conjunction of two separate "
                        + "bounds, one placing m below M and the other placing n below M. Each bound puts its "
                        + "operand inside the canonical residue range from zero up to but excluding M, where "
                        + "the remainder map acts as the identity and returns the operand unchanged. The two "
                        + "readings therefore equal the operands themselves, and their inequality is exactly "
                        + "the given distinctness of m and n transported across the two identities. The "
                        + "argument is purely arithmetic and logical: it invokes only the identity behaviour "
                        + "of the remainder on its canonical range and asserts no numerical certificate.")))
            ))));
}
