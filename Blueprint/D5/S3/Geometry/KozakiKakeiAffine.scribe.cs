using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiAffineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiAffine.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each matching uses the chosen coordinate once, so its polynomial is at most linear in that coordinate.",
        H("Isolating a coordinate in a matching"),
        Blocks(
            Definition("Rest", "Remaining coordinates",
                "The remaining coordinate set omits the distinguished index."),
            Definition("Coeff", "Coefficient ring",
                "Coefficients are complex multivariate polynomials in the remaining coordinates."),
            Definition("isolate", "Single-variable presentation",
                "The chosen variable is extracted as the outer polynomial variable via the option-type decomposition."),
            Theorem("isolate_X_self", "The distinguished variable",
                "The variable at the chosen index becomes the outer indeterminate."),
            Theorem("isolate_X_other", "A remaining variable",
                "A variable at a different index becomes a constant coefficient in the outer polynomial."),
            Theorem("eval_isolate", "Evaluation after isolation",
                "Evaluation at the full assignment equals evaluation of the outer polynomial after evaluating its coefficients at the remaining assignment."),
            Theorem("diff_prime", "Prime coordinate differences",
                "An oriented difference of two distinct variables is prime. Isolate the second variable to turn the factor into a monic linear polynomial."),
            Theorem("diff_not_dvd_of_edges_ne", "Different unordered pairs give independent factors",
                "Collapse the two coordinates of the divisor to one value and keep the coordinates of the other edge apart. The divisor vanishes but the other factor does not."),
            Definition("remainingVertex", "Vertices away from an edge",
                "Each endpoint of a different matching edge survives removal of the distinguished vertex."),
            Definition("remainingProduct", "Product off the distinguished edge",
                "The product uses precisely the edges other than the distinguished edge."),
            Theorem("matching_isolate_left", "Isolation at the first endpoint",
                "The linear coefficient is the negative of the remaining product. The constant coefficient is the second endpoint variable times the remaining product."),
            Theorem("matching_isolate_right", "Isolation at the second endpoint",
                "The linear coefficient is the remaining product. The constant coefficient is the negative of the first endpoint variable times the remaining product."),
            Theorem("matching_exists_linear", "Linearity in every coordinate",
                "Find the matching edge and endpoint containing the chosen coordinate and apply its ordered isolation formula."),
            Theorem("rename_matchingPolynomial", "Transport of matching factors",
                "Renaming the polynomial variables composes the endpoint labeling with the permutation."),
            Theorem("rename_F_exists_linear", "Linearity after a permutation",
                "The difference of the two transported matching products is at most linear in the chosen coordinate."))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static string NodeId(string name) =>
        "frieze-affine-" + name.ToLowerInvariant().Replace('_', '-');
}
