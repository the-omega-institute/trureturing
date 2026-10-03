using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class FieldNormalProductLocalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FieldNormalProductLocality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite residue cancellation preserves locality for the actual Fock state fields.",
        H("Ordered Product Locality"),
        Blocks(
            Paragraph(Text("The two residue halves have pointwise finite support. "
                + "Polynomial shifts act on coefficient functions, without a "
                + "multivariable completion or an assumption of normal-product "
                + "associativity. Both preservation results are consumed by the "
                + "unrestricted polynomial Fock state-field construction.")),
            Describe.Lean(
                DescribeId.Create("normal-minus-one-locality"),
                DeclarationHandle.Create(Prefix + "normalMinusOne_locality"),
                H("The sum of three locality orders suffices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For three pairwise local fields A, B and C, "
                    + "the ordered minus-one product of A and B is local with C. "
                    + "The sufficient order is the sum of the A-C, B-C and A-B "
                    + "orders, independently of the vector. The residue boundary "
                    + "and binomial cancellation are proved, not assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("divided-derivative-locality"),
                DeclarationHandle.Create(Prefix + "dividedDerivative_locality"),
                H("Hasse differentiation preserves locality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The kth divided derivative increases a "
                    + "sufficient locality order by k. The proof differentiates the "
                    + "annihilating coefficient polynomial, then uses the pinned "
                    + "LaurentSeries derivative-iterate identity and the nonzero "
                    + "complex factorial. No upstream commented sketch is imported."))),
                DescribeRole.Theorem))));
}
