using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.CollisionAnalytic;

internal sealed class AbsoluteEvaluationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/CollisionAnalytic/AbsoluteEvaluation.";
    private static readonly LibraryNoteRef LocalityBackground =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute numerical evaluation of finite collision-localized Laurent expressions in each ordered radial chamber.",
        H("Absolute evaluation of ordered collision expansions"),
        Blocks(
            Paragraph(Text("Let P be a finite labelled Laurent polynomial over the complex numbers, and let each "
                + "pair of distinct labels have its own nonnegative integer pole order. For a permutation sigma, "
                + "take nonzero complex coordinates whose norms strictly decrease in the sigma order. "
                + "The coefficients are those of the existing complete ordered Hahn expansion of P divided "
                + "by the product of the fixed-label collision differences raised to these orders.")),
            Describe.Lean(
                DescribeId.Create("collisionabsoluteevaluation-monomial-family"),
                DeclarationHandle.Create(Prefix + "monomial_family"),
                H("Formal coefficient fibers and absolute numerical regrouping"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(Paragraph(Text("A formally summable family of Hahn monomials has finite nonzero "
                    + "coefficient fibers. If the numerical monomials form an absolutely summable family, "
                    + "each formal coefficient times its numerical Laurent weight equals the topological "
                    + "sum over the corresponding exponent fiber. Grouping an absolutely summable family "
                    + "by this map preserves its sum, and the triangle inequality bounds the grouped "
                    + "absolute sum by the ungrouped absolute sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("collisionabsoluteevaluation-collision-absolute-evaluation"),
                DeclarationHandle.Create(Prefix + "collision_absolute_evaluation"),
                H("All integer coefficients evaluate to the Laurent quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LocalityBackground),
                Blocks(Paragraph(Text("The sum ranges over all labelled integer exponent vectors. It is "
                    + "absolutely summable and has value P(z) divided by the collision denominator, which "
                    + "is nonzero on the chamber. Its absolute sum is at most the finite absolute Laurent "
                    + "numerator value multiplied by the inverse pole powers of the radial gaps "
                    + "abs(norm(z_i)-norm(z_j)). These are radial gaps, not complex collision distances. "
                    + "Zero pole orders contribute one; negative numerator exponents require the stated "
                    + "nonzero coordinates. Reversing the order of a fixed-label difference retains its "
                    + "minus sign before taking its pole power."))),
                DescribeRole.Theorem),
            Paragraph(Text("The argument reuses mathlib formal Hahn sums and their finite antidiagonal "
                + "multiplication, together with complex geometric-series convergence and absolute product "
                + "sums. Finite powers of the geometric inverse supply every pole order, so no additional "
                + "one-variable binomial convergence theorem is needed. Hahn series and their summable "
                + "families are by Aaron Anderson; the numerical infinite-sum machinery includes work by "
                + "Anatole Dedecker and the mathlib contributors, under Apache 2.0. Matsuo--Nagatomo is "
                + "local-field background and does not supply this Lean evaluation theorem. No claim of "
                + "literature novelty is made.")),
            Paragraph(Text("The chamber is nonempty: assign the coordinate with sigma position i the "
                + "positive integer n-i. Collision avoidance alone is insufficient for a chosen ordered "
                + "series. No evaluation homomorphism on the entire fraction field is asserted. "
                + "Homogeneous matrix-coefficient slices may be evaluated by this result when their "
                + "coefficients equal the displayed ordered expansion. Convergence of an infinite sum "
                + "over all homogeneous slices requires a further finite-energy or growth argument.")))));
}
