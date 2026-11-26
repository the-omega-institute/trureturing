using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.HilbertSmith;

internal sealed class NestedResidueMatchingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/HilbertSmith/NestedResidueMatching.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single pair of index sets minimizes the squared residue discrepancy at every prime-power level.",
        H("Nested residue matching"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simultaneous-minimizer"),
                DeclarationHandle.Create(Prefix + "simultaneous_minimizer"),
                H("Simultaneous minimization for nested labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take two finite sets of equal size, with a label on each element at each level "
                        + "from zero through e. Labels on the two sets lie in their specified finite sets. A pair "
                        + "of inputs with equal labels at one level has equal labels at the next level, "
                        + "including inputs outside the finite sets. Every pair from the two sets "
                        + "has equal labels at level e. Suppose the two full counts of each label "
                        + "differ by at most one at every level.")),
                    Paragraph(Text(
                        "For each k at most the common size, there are two subsets of size k whose "
                        + "sum of squared label-count differences at every level equals twice the "
                        + "truncated difference between k and the full matching capacity. The capacity "
                        + "is the sum, over labels, of the smaller of the two full counts.")),
                    Paragraph(Text(
                        "Extend a matching at each level until no two unused compatible endpoints "
                        + "remain. The resulting matchings are nested. A size-k selection comparable "
                        + "by inclusion with each of them uses only matched edges below capacity. "
                        + "Above capacity it contains all matched edges, and each label has at most "
                        + "one leftover endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflected-congruence"),
                DeclarationHandle.Create(Prefix + "reflected_eq_iff_dvd"),
                H("Reflection and divisibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive modulus q, the reflected residue of j is q minus one "
                    + "minus the ordinary residue of j. The row residue of i equals this "
                    + "reflected residue exactly when q divides i+j+1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflected-equality"),
                DeclarationHandle.Create(Prefix + "reflected_eq_reflected_iff"),
                H("Equality after reflection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive modulus, two indices have equal reflected residues exactly "
                    + "when their ordinary residues are equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reflected-capacity"),
                DeclarationHandle.Create(Prefix + "reflected_capacity"),
                H("Capacity of the reflected residue intervals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n nonnegative and q positive, write r for the remainder of n modulo q. "
                    + "The matching capacity of two intervals of indices from zero through n-1 "
                    + "with ordinary row residues and reflected column residues is n minus the "
                    + "minimum of r and q-r. The extra occurrences above the common quotient "
                    + "appear at the first r row residues and the last r column residues."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("residue-loss-lower"),
                DeclarationHandle.Create(Prefix + "residue_loss_lower"),
                H("Lower bound at one modulus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At each positive modulus q, any two size-k subsets of the index interval "
                    + "have squared residue discrepancy at least twice the positive part of "
                    + "k minus the reflected capacity. The discrepancy is the sum of squared "
                    + "differences of the ordinary row counts and reflected column counts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("residue-minimizer"),
                DeclarationHandle.Create(Prefix + "exists_residue_minimizer"),
                H("Exact minima at all powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive natural base p, every nonnegative height e, and every "
                    + "k at most n, one pair of size-k subsets attains the lower bound at all "
                    + "moduli p to the power a with zero through e as exponents. Order the "
                    + "levels from the largest modulus down to one and use the nested matching. "
                    + "This choice supplies simultaneous local equality for the residue counts "
                    + "of Hilbert minors."))),
                DescribeRole.Theorem))));
}
