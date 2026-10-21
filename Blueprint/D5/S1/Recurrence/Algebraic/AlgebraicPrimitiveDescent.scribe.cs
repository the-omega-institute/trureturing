using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class AlgebraicPrimitiveDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An algebraic primitive of an element of a characteristic-zero differential field can be replaced by a primitive in that field.",
        H("Descent of Algebraic Primitives"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("algebraic-primitive-descent-existence"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/AlgebraicPrimitiveDescent.exists_primitive_of_isAlgebraic"),
                H("A primitive in the base field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let K be a differential field of characteristic zero and let L be a nonzero commutative differential K-algebra whose derivative extends that of K. "
                    + "For x in L and g in K, suppose x is algebraic over K and x' is the image of g. Then there is h in K with h'=g. "
                    + "To see this, write the monic minimal polynomial of x as P(Y)=Y^n+aY^(n-1)+lower terms, with n positive. "
                    + "Differentiating P(x)=0 gives a second polynomial relation Q(x)=0, where Q is the coefficient derivative of P plus g times its formal polynomial derivative. "
                    + "The leading coefficient of P is one, so Q has degree less than n; minimality forces Q to vanish identically. "
                    + "Its coefficient of Y^(n-1) is a'+ng, and therefore h=-a/n is the required primitive. "
                    + "This proof is repository-derived and uses the coefficient-wise derivation and minimal-polynomial results from Mathlib."))),
                DescribeRole.Theorem))));
}
