using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class PolynomialFockJacobiDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/PolynomialFockJacobi.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual polynomial Fock fields satisfy integer residue closure and Borcherds identity.",
        H("Integer Fock Composition"),
        Blocks(
            Paragraph(Text("Every state is an arbitrary complex polynomial in the countable "
                + "Fock variables. Every mode parameter is an integer. Residues are genuine "
                + "lower-truncated operator fields, with both coefficient sums finite on "
                + "each input state. Generalized integer binomial coefficients and integer "
                + "powers of minus one retain the negative-mode conventions. No bounded "
                + "degree, second state-field map or assumed reconstruction law is used. "
                + "This rank-one formal construction does not establish a Monster "
                + "realization, module fusion, analytic CFT or spacetime dynamics.")),
            Describe.Lean(
                DescribeId.Create("fock-residue-nonnegative-locality"),
                DeclarationHandle.Create(Prefix + "residue_nonnegative_locality"),
                H("Nonnegative residues obey Dong cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The double commutator is killed by the first "
                    + "pair's locality polynomial and by the product of the other two "
                    + "locality polynomials. Expanding the commuting coefficient shifts "
                    + "annihilates every finite term, giving an order independent of "
                    + "the vector. Evaluation gives locality of the actual residue field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fock-relative-vacuum-uniqueness"),
                DeclarationHandle.Create(Prefix + "relative_vacuum_uniqueness"),
                H("Vacuum uniqueness relative to the existing Y"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A creative field covariant under the actual L(-1), "
                    + "with zero initial vacuum state and local with every Y(u), is zero. "
                    + "The covariance recurrence kills the entire vacuum series. Extracting "
                    + "the other field's constant vacuum coefficient in locality kills "
                    + "every coefficient on every state. Membership in the image of Y "
                    + "is not a hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fock-integer-residue-closure"),
                DeclarationHandle.Create(Prefix + "residue_closure"),
                H("The same Y is closed under every integer residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Y(mu(a,r,b)) equals R_r(Y(a),Y(b)) for every "
                    + "integer r. Nonnegative Dong cancellation and negative "
                    + "divided-derivative normal-product locality give relative locality. "
                    + "Supported coefficient telescoping proves covariance; vacuum "
                    + "coefficients prove creativity and initial state mu(a,r,b). "
                    + "Relative uniqueness identifies the resulting operator with Y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fock-all-integer-borcherds"),
                DeclarationHandle.Create(Prefix + "borcherds"),
                H("Borcherds identity for all states and integer modes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The left iterate sum and both composition branches "
                    + "have separate pointwise finite support. Closure supplies the p=0 "
                    + "seed; actual pairwise locality supplies the high-r region. "
                    + "Supported Pascal reindexing gives the three-term discrepancy "
                    + "recurrence. Induction on positive p and nested induction on "
                    + "negative p and the finite distance below the high-r boundary "
                    + "prove the exact law for every integer p,q,r."))),
                DescribeRole.Theorem))));
}
