using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.PeriodicOrbits;

internal sealed class ProductClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direct products multiply fixed-point tables and preserve the finite Dold divisibility obstruction.",
        H("Product closure for finite periodic actions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fixed-count-product"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/ProductClosure.fixed_count_prodMap"),
                H("Fixed points of a direct product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic")),
                Blocks(
                    Paragraph(Text(
                        "For finite carriers X and Y and self-maps f and g, the n-th iterate of "
                        + "the direct product action (f,g) fixes exactly the Cartesian product "
                        + "of the points fixed by f^n and g^n. Hence its fixed-point count is "
                        + "the pointwise product of the two fixed-point counts.")),
                    Paragraph(Text(
                        "The proof is an explicit equivalence between the fixed-point subtype of "
                        + "Prod.map f g and the product of the two fixed-point subtypes. It uses "
                        + "the actual iterate identity for Prod.map, so it records the group-action "
                        + "product rather than merely multiplying two natural numbers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("product-dold-closure"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/ProductClosure.product_dold_nonneg_dvd"),
                H("Dold nonnegativity survives direct products"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic")),
                Blocks(
                    Paragraph(Text(
                        "The pointwise product of the fixed-count sequences of two finite "
                        + "actions again has a nonnegative, period-divisible Mobius transform. "
                        + "This is the arithmetic shadow of the direct-product action: apply "
                        + "the actual orbit-counting Mobius identity to Prod.map f g and use "
                        + "the fixed-count product theorem.")),
                    Paragraph(Text(
                        "Thus Dold's obstruction is closed under products of finite cyclic "
                        + "actions. The result is stronger than an abstract multiplication "
                        + "identity because it obtains positivity and divisibility from an "
                        + "explicit finite dynamical realization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-table-product-dold"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/ProductClosure.finite_table_product_dold"),
                H("Divisor-table product consumer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/FiniteGroups/puri2001arithmetic")),
                Blocks(
                    Paragraph(Text(
                        "If two tables are realized on finite cyclic actions through the divisors "
                        + "of a positive exponent M, then their pointwise product satisfies the "
                        + "same nonnegative and divisible Mobius conditions at every divisor of M. "
                        + "The table equalities are transported term by term through the finite "
                        + "divisor antidiagonal, giving a reusable consumer for products of "
                        + "periodic systems."))),
                DescribeRole.Theorem)
        )));
}
