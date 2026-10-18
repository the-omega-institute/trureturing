using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class SharpSliceAverageRefutationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Geometry/Hyperideal/SharpSliceAverageRefutation.sharp_slice_average_refutation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational determinant certificates for sharp-slice averaging.",
        H("Averaging can reverse the determinant test"),
        Blocks(
            Paragraph(Text(
                "Use the fixed character-coordinate Gram matrix gram with slot order "
                + "(12,13,14,34,24,23). The asymmetric vector has parameters "
                + "(r,o,A,B,xi,zeta)=(49/10,49/10,2,2,4/5,0), while its C2 average "
                + "has the same first four parameters and xi=zeta=0.")),
            Describe.Lean(
                DescribeId.Create("sharp-slice-average-refutation"),
                DeclarationHandle.Create(Declaration),
                H("Exact determinant reversal"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The statement refutes the implication that a negative "
                        + "determinant for the averaged vector forces a negative "
                        + "determinant for the asymmetric vector. The averaged value is "
                        + "-274999/10000 and the asymmetric value is 189/80.")),
                    Paragraph(Text(
                        "Both values are exact rational evaluations of the displayed "
                        + "finite Gram determinant, so the reversal does not rely on a "
                        + "numerical approximation or on a global realization claim."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var r = Fraction(Num(49), Num(10));
        var original = Call("det", Call("gram", r, r, F.D(2), F.D(2),
            Fraction(F.D(4), F.D(5)), F.D(0)));
        var average = Call("det", Call("gram", r, r, F.D(2), F.D(2),
            F.D(0), F.D(0)));
        var implication = new Formula.Logic(
            Lt(average, F.D(0)), FormulaLogicOperator.Implies, Lt(original, F.D(0)));
        return new Formula.Not(implication);
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
}
