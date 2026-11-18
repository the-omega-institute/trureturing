using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.QuadraticFields;

internal sealed class QuadraticAccumulationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/dhandahaynes2025accumulation");

    private static DocumentBlock Item(string selector, string description, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("quadraticaccumulation-" + selector.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Arith/QuadraticFields/QuadraticAccumulation." + selector),
            H(selector), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(description))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every signed nonzero norm value of the trace dual is approached by distinct normalized quadratic approximations.",
        H("Quadratic approximation and trace-dual norms"), Blocks(
            Paragraph(Text("Dhanda and Haynes, Theorem 4, classify the complete accumulation set of normalized approximations to a real quadratic irrational. The result below proves the norm-value inclusion. The exclusion of all other accumulation points is not asserted here.")),
            Paragraph(Text("The radicand is an arbitrary squarefree integer at least two. The constant and square-root coefficients are rational, and the latter is nonzero. Denominators range over all nonzero integers and numerators over all integers; there is no coprimality hypothesis.")),
            Item("K", "The rational quadratic algebra has distinguished generator whose square is the radicand. Under the stated hypotheses it is a field.", DescribeRole.Definition),
            Item("alpha", "The irrational is represented by its constant and square-root coordinates.", DescribeRole.Definition),
            Item("lattice", "The integer lattice is the span of one and the quadratic irrational.", DescribeRole.Definition),
            Item("traceDual", "The dual is defined by integrality of the actual algebra trace pairing with every element of the lattice.", DescribeRole.Definition),
            Item("approximationValues", "The signed normalized error multiplies the error by the absolute value of its integer denominator. This is a set of real values.", DescribeRole.Definition),
            Item("realEmbedding", "The real algebra homomorphism sends the distinguished generator to the positive square root.", DescribeRole.Definition),
            Item("RealField", "The actual intermediate field of the real numbers is generated over the rationals by the irrational.", DescribeRole.Definition),
            Item("realAlpha", "The irrational is regarded as an element of its generated real subfield.", DescribeRole.Definition),
            Item("realLattice", "The integer span of one and the irrational lies inside the actual generated real field.", DescribeRole.Definition),
            Item("realTraceDual", "The original lattice is dualized using the actual trace form of the generated real field.", DescribeRole.Definition),
            Item("coordinateEquiv", "The coordinate algebra is faithfully identified with the generated real subfield. The inverse recovers the square root by subtracting the rational constant and dividing by the nonzero square-root coefficient.", DescribeRole.Definition),
            Item("HasDistinctApproximationSequence", "An injective sequence lies in the specified set, avoids its proposed limit, and converges to that limit. This condition implies genuine set accumulation.", DescribeRole.Definition),
            Item("signed_norm_values_accumulate", "For every nonzero element of the trace dual in the actual generated real subfield, multiply its field norm by twice the rational square-root coefficient and the positive square root of the radicand. Both signs of this value admit injective sequences of normalized approximation values avoiding the limit, and are genuine set accumulation points.", DescribeRole.Theorem),
            Paragraph(Text("Trace integrality gives an integer denominator and numerator from every dual vector. Clearing the three rational multiplication coefficients and applying the positive Pell existence theorem produces a norm-one multiplier preserving the exact dual lattice. Its positive real embedding exceeds one and its conjugate is its reciprocal. Powers of the multiplier expand one embedding and contract the other.")),
            Paragraph(Text("After a finite shift the denominators are positive. The normalized values equal their limiting scaled norm plus a nonzero geometric correction. This correction proves injectivity and exclusion of the limit itself. Negating both integer coordinates produces the opposite signed limit. Algebra traces and norms are computed through the coordinate basis and transported by an algebra equivalence to the actual generated real subfield.")))));
}
