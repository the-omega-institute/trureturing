using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class BinaryBaselineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var complex = Id("C");
        var naturals = Id("N");
        var n = Id("n");
        var recurrence = Id("Rbinary");
        var solutionSpace = Call("Sol", recurrence);
        var characteristicPolynomial = Call("charPoly", recurrence);
        var geometricTerm = new Formula.Power(Num(2), n);
        var geometricSequence = new Formula.Sequence(geometricTerm, n, naturals);
        var firstOrder = new Formula.Logic(
            Equal(Call("order", recurrence), Num(1)),
            FormulaLogicOperator.And,
            Call("IsSolution", recurrence, geometricSequence));
        var oneDimensional = Equal(
            Call("dim", complex, solutionSpace),
            Num(1));
        var uniqueRoot = Equal(
            Call("roots", characteristicPolynomial),
            new Formula.SetLiteral([Num(2)]));
        var fingerprintOne = Equal(Id("binaryCodingFingerprint"), Num(1));
        var package = new Formula.Logic(
            firstOrder,
            FormulaLogicOperator.And,
            new Formula.Logic(
                oneDimensional,
                FormulaLogicOperator.And,
                new Formula.Logic(
                    uniqueRoot,
                    FormulaLogicOperator.And,
                    fingerprintOne)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The binary geometric baseline has order one, a one-dimensional solution space, "
                + "one characteristic root, and fingerprint one.",
            H("Binary Geometric Baseline"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("binary-geometric-recurrence-first-order"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/BinaryBaseline."
                        + "binary_geometric_recurrence_first_order"),
                    H("The binary geometric recurrence is first order"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(firstOrder)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The recurrence has order one, and the geometric sequence with nth "
                            + "term two to the n is a solution. Thus each next term depends "
                            + "only on the immediately preceding term."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("binary-recurrence-solution-space-finrank"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/BinaryBaseline."
                        + "binary_recurrence_solution_space_finrank"),
                    H("The binary recurrence solution space is one-dimensional"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(oneDimensional)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The standard initial-value basis identifies the solution space with "
                            + "one complex initial coordinate, so its finite dimension is one."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("binary-characteristic-roots"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/BinaryBaseline."
                        + "binary_characteristic_roots"),
                    H("The binary characteristic polynomial has exactly one root"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(uniqueRoot)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The characteristic polynomial is X minus two, and its root multiset "
                            + "is the singleton containing two. This is the formal "
                            + "no-hidden-face assertion."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("binary-baseline-package"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/BinaryBaseline.binary_baseline_package"),
                    H("Binary baseline package"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(package)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The order-one recurrence, one-dimensional solution space, and "
                                + "singleton characteristic root are conjoined with the frozen "
                                + "binary coding fingerprint value one.")),
                        Paragraph(Text(
                            "The singleton root is the precise no-hidden-face content. The "
                                + "source phrase collapse back to zeta itself is not formalized: "
                                + "the imported S0 interfaces provide no corresponding zeta-layer "
                                + "object or two-sided construction, so no zeta claim appears in "
                                + "this package."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Champions/CodingFingerprint")),
            ]));
    }
}
