using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices;

internal sealed class CyclotomicTraceSumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/grayson1984semistability");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal sums of trace ideal lattices",
        H("Multiplicative covolume and additive degree"),
        Blocks(
            Describe.Lean(DescribeId.Create("orthogonal-trace-ideal-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/CyclotomicTraceSum.trace_sum_formula"),
                H("The discriminant slope shift is independent of the number of summands"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let K be a number field of degree d and discriminant D. "
                        + "For a finite family of n invertible fractional ideals of its "
                        + "ring of integers, take the actual coordinatewise ideal lattice "
                        + "inside the Euclidean orthogonal sum of their trace spaces. "
                        + "Each ideal has the standard Hermitian norm at every embedding. "
                        + "The squared ambient norm is the sum of the squared summand norms.")),
                    Paragraph(Text("Choose an integral basis in each ideal, indexed by d "
                        + "elements, and insert each basis vector into its summand. These "
                        + "vectors form an integral basis of the sum lattice. Vectors "
                        + "in different summands are orthogonal, so their full Gram "
                        + "matrix is block diagonal. Its determinant is the product "
                        + "of the summand Gram determinants. Positivity permits taking "
                        + "square roots, giving the product of the actual covolumes. "
                        + "This is the coordinate-support Gram factorization also "
                        + "expressed by NumberField.det_gram_pi in "
                        + "NumberFieldIntegralLattice. That theorem uses Fin-indexed "
                        + "real bases; here an arbitrary finite index type and integral "
                        + "lattice bases require the PiLp coordinate interface. The "
                        + "matrix identity sum_gram provides precisely that interface, "
                        + "and Matrix.det_blockDiagonal supplies its determinant. "
                        + "The block-diagonal calculation is an application of these "
                        + "existing formulas.")),
                    Paragraph(Text("The result is the positive square root of the "
                        + "absolute discriminant to the power n, multiplied by the "
                        + "exponential of minus the sum of the ideal degrees. This is "
                        + "the discriminant to the power n over two times the exponential "
                        + "of minus the direct sum degree. The integral rank is d times n. "
                        + "When n is positive, minus log of the covolume divided by this "
                        + "rank equals the normalized direct sum degree minus log of the "
                        + "absolute discriminant divided by twice d. The covolume and "
                        + "rank formulas also include the empty sum.")),
                    Paragraph(Text("This construction uses the fractional ideal trace "
                        + "covolume formula and the Euclidean Gram definition directly. "
                        + "It treats genuine orthogonal sums, and does not impose an "
                        + "orthogonal ideal decomposition on an arbitrary Hermitian "
                        + "module."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equal-degree-cyclotomic-ideal-sum-hn"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Lattices/CyclotomicTraceSum.equal_degree_sum_hn"),
                H("Equal-degree orthogonal ideal sums are semistable"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Suppose K is a full cyclotomic field, the family "
                        + "is nonempty, and every ideal degree equals the same real "
                        + "number a. The orthogonal sum is then semistable over the "
                        + "integers, and its HN endpoint list is uniquely the singleton "
                        + "consisting of the whole lattice. Its normalized slope is "
                        + "a divided by d minus "
                        + "the discriminant shift. The ideals need not coincide or "
                        + "be principal. The common degree hypothesis is used to "
                        + "compare each coordinate slope with the mean slope of "
                        + "the entire sum. The cyclotomic instance supplies the "
                        + "primitive root internally in the ideal semistability "
                        + "theorem, so no root needs to be specified for this sum.")),
                    Paragraph(Text("Take the first nonzero HN factor and choose a "
                        + "nonzero coordinate of one of its vectors. Coordinate "
                        + "projection is an integral map of operator norm at most "
                        + "one to the corresponding ideal. The Euclidean morphism "
                        + "slope bound compares the factor's slope to the slope "
                        + "of that semistable cyclotomic ideal. The exact direct "
                        + "sum covolume and rank identify the latter with the mean "
                        + "slope of the sum. Since the first HN factor already "
                        + "has maximal slope among all sublattices, the required "
                        + "semistability inequality follows for every sublattice. "
                        + "Semistability constructs the singleton HN chain, and "
                        + "uniqueness identifies every HN chain with it. "
                        + "This is a Euclidean direct sum argument; it does not "
                        + "assert semistability for a general Hermitian metric "
                        + "on the same algebraic module."))),
                DescribeRole.Theorem))));
}
