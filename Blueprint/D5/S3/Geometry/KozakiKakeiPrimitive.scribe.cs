using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KozakiKakeiPrimitiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KozakiKakeiPrimitive.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal orientation of the closing factor is used when isolating the first coordinate.",
        H("Relative primeness of the signed coefficients"),
        Blocks(
            Definition("zeroEdge", "Distinguished matching edge",
                "The distinguished edge has index zero in each matching."),
            Definition("nextCoord", "Second coordinate",
                "The second column survives removal of the first column from the variable set."),
            Definition("lastCoord", "Closing coordinate",
                "The last column survives removal of the first column from the variable set."),
            Definition("middleCoord", "Third coordinate",
                "The third column survives removal of the first column from the variable set."),
            Definition("oddRest", "Remaining odd endpoints",
                "These are the odd matching endpoints outside the distinguished edge."),
            Definition("evenRest", "Remaining even endpoints",
                "These are the even matching endpoints outside the distinguished edge."),
            Definition("U", "Odd tail product",
                "Multiply the oriented factors of the remaining odd edges."),
            Definition("V", "Even tail product",
                "Multiply the oriented factors of the remaining even edges."),
            Definition("A", "Linear coefficient",
                "The coefficient of the first coordinate is the odd tail product minus the even tail product."),
            Definition("B", "Constant coefficient",
                "The constant coefficient is the last coordinate times the even tail product minus the second coordinate times the odd tail product."),
            Theorem("isolate_F", "The two signed coefficients",
                "Isolating the first column variable gives the linear polynomial with coefficients A and B.",
                IsolateF()),
            Theorem("signed_four_coefficient", "Four-column coefficient",
                "The linear coefficient is the sum of the last and second variables minus twice the third. Both tail products have one factor.",
                SignedFourCoefficient()),
            Theorem("primitive_coefficients", "Nonzero relatively prime coefficients",
                "Off order six, a common prime must divide the difference between the second and last coordinates. Identifying those two coordinates leaves the linear coefficient nonzero, with a separate specialization at order four.",
                PrimitiveCoefficients()),
            Theorem("A_not_unit", "The linear coefficient is a nonunit",
                "Evaluation with every remaining coordinate zero sends each nonempty tail product to zero.",
                ANotUnit()))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Theorem(string name, string title, string prose, Formula statement) =>
        Describe.Lean(DescribeId.Create(NodeId(name)), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(StrataLint.Scribe.DefinitionDsl.Text(prose))), DescribeRole.Theorem);

    private static Formula IsolateF() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, D(2), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, Word("isolate"), Open, Word("first"), Open, F.Id("m"), Close, Comma,
        F.Id("F"), Open, F.Id("m"), Close, Close, Sp, Eq, Sp, Word("PolynomialC"), Open, F.Id("A"), Open,
        F.Id("m"), Close, Close, Sp, Cdot, Sp, Word("PolynomialX"), Sp, Plus, Sp, Word("PolynomialC"), Open,
        F.Id("B"), Open, F.Id("m"), Close, Close);

    private static Formula SignedFourCoefficient() => Seq(
        F.Id("A"), Open, D(2), Close, Sp, Eq, Sp, F.Id("X"), Open, Word("lastCoord"), Open, D(2), Close, Close,
        Sp, Plus, Sp, F.Id("X"), Open, Word("nextCoord"), Open, D(2), Close, Close, Sp, Minus, Sp, D(2), Sp,
        Cdot, Sp, F.Id("X"), Open, Word("middleCoord"), Open, D(2), Close, Close);

    private static Formula PrimitiveCoefficients() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, D(2), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, F.Id("m"), Sp, Neq, Sp, D(3), Sp, Implies, Sp, F.Id("A"), Open, F.Id("m"),
        Close, Sp, Neq, Sp, D(0), Sp, Land, Sp, Word("IsRelPrime"), Open, F.Id("A"), Open, F.Id("m"), Close,
        Comma, F.Id("B"), Open, F.Id("m"), Close, Close);

    private static Formula ANotUnit() => Seq(
        Forall, Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, D(2), Sp, Le, Sp,
        F.Id("m"), Sp, Implies, Sp, Neg, Word("IsUnit"), Open, F.Id("A"), Open, F.Id("m"), Close, Close);

    private static Formula Word(string value) => Seq(Operatorname, Grp(F.Id(value)));

    private static string NodeId(string name) =>
        "frieze-primitive-" + name.ToLowerInvariant().Replace('_', '-');
}
