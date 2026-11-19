using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class PersistentLaplacianHeatStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/PersistentLaplacianHeatStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pairwise heat stability of the degree-zero weighted persistent Laplacian.",
        H("Degree-zero persistent heat stability"),
        Blocks(
            Describe.Lean(DescribeId.Create("weighted-persistent-laplacian"),
                DeclarationHandle.Create(Prefix + "persistentLaplacian"),
                H("The weighted persistent vertex operator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite simplicial complexes K contained in L on a linearly ordered vertex type, "
                    + "take the real coordinates of the integer ordered edge boundary of L. An increasing "
                    + "edge contributes its two signed vertex deletions. Multiply the column of each edge "
                    + "by the square root of its weight and divide the row of each vertex by the square "
                    + "root of its weight. Let B and C be the resulting retained and hidden rows. "
                    + "Restrict B to the kernel of C to obtain T. The degree-zero unaugmented persistent "
                    + "Laplacian is S = TT*, equivalently B times the orthogonal projection onto the "
                    + "kernel of C times B*."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("weighted-persistent-heat-stability"),
                DeclarationHandle.Create(Prefix + "weighted_persistent_heat_stability"),
                H("Comparison at two positive times"),
                StatementSource.FromAuthor(Disp(Bound())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use one fixed positive retained vertex weight system, any two positive hidden "
                        + "vertex weight systems, and positive edge weights w and w' on L. For t,u > 0 "
                        + "and M ≥ 1, assume for each edge e that t w(e) divided by M is at most u w'(e), "
                        + "which is at most M t w(e). Here S and S' are the corresponding persistent "
                        + "Laplacians on the same retained Euclidean coordinates. The norm is the "
                        + "Euclidean operator norm. Singular hidden blocks and empty face sets are included.")),
                    Paragraph(Text(
                        "The quadratic form of S is the squared distance from B*x to the range of C*. "
                        + "The hidden vertex factors are invertible row scalings, so their adjoints can "
                        + "be absorbed into the variable of the distance minimization. Comparing the same "
                        + "trial vector with effective edge weights t w and u w' gives the two Löwner bounds.")),
                    Paragraph(Text(
                        "The two positive forms from the Löwner bounds yield a mixed quadratic estimate "
                        + "between the two generators. Apply it to the derivative of the product with "
                        + "one heat factor running forward and the other backward. Cauchy–Schwarz in time "
                        + "bounds the pairing by the product of heat energies. Each energy keeps its "
                        + "endpoint norm term. For a unit vector the two heat expectations are nonnegative, "
                        + "so the larger endpoint norm bounds their absolute difference. Substitution into "
                        + "the energy bound and the self-adjoint Rayleigh formula give the stated constant."))),
                DescribeRole.Theorem))));

    private static Formula Bound()
    {
        Formula m = F.Id("M");
        Formula gap = Seq(Heat("u", Seq(F.Id("S"), Apos)), Sp, Minus, Sp, Heat("t", F.Id("S")));
        return new Formula.Relation(new Formula.Norm(gap), FormulaRelationOperator.LessThanOrEqual,
            new Formula.Fraction(Seq(m, Minus, D(1)), Seq(m, Plus, D(1))));
    }

    private static Formula Heat(string time, Formula generator) =>
        new Formula.FunctionCall(FormulaIdentifier.Create("exp"), [Seq(Minus, F.Id(time), Sp, generator)]);
}
