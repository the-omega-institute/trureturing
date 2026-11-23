using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class DegreeSpectrumPackingDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/DegreeSpectrumPacking";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The width of a frequency band forces a close pair of sums at fixed degree.",
        H("A Packing Bound for Finite Frequency Sums"),
        Blocks(
            Paragraph(Text(
                "Let g on a finite index set J take values in the closed interval [a,b]. Let p be a natural number and M the multiset coefficient "
                + "multichoose(|J|,p), and assume M≥2. For a nonnegative integer "
                + "count vector m write F(m)=Σ m(j)g(j) and d(m)=Σ m(j).")),
            Describe.Lean(
                DescribeId.Create("exists-close-degree-vectors"),
                DeclarationHandle.Create(Owner + ".exists_close_degree_vectors"),
                H("Two distinct degree vectors have nearby frequencies"),
                StatementSource.FromAuthor(Gap()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There are M degree vectors by stars and bars. If any two give "
                        + "the same frequency, they have zero gap. Otherwise order the M "
                        + "values in [pa,pb]. The M−1 adjacent differences sum to at most "
                        + "p(b−a), and at least one is at most their mean upper bound.")),
                    Paragraph(Text(
                        "For two endpoints a and b, the degree-p sums run through an "
                        + "arithmetic progression. The bound is attained. The existence of "
                        + "a close pair constrains possible uniform gap hypotheses. A "
                        + "weighted near-collision bound also needs control of the weights "
                        + "on all such pairs."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula Gap()
    {
        var p = F.Id("p");
        var m = F.Id("m");
        var n = F.Id("n");
        var count = F.Id("M");
        var difference = new Formula.Absolute(Seq(Call("F", m), Minus, Call("F", n)));
        var bound = new Formula.Fraction(Multiply(p, Seq(Open, F.Id("b"), Minus, F.Id("a"), Close)),
            Seq(count, Minus, D(1)));
        var different = new Formula.Relation(m, FormulaRelationOperator.NotEqual, n);
        var degreeM = new Formula.Relation(Call("d", m), FormulaRelationOperator.Equal, p);
        var degreeN = new Formula.Relation(Call("d", n), FormulaRelationOperator.Equal, p);
        var close = new Formula.Relation(difference, FormulaRelationOperator.LessThanOrEqual, bound);
        var conditions = new Formula.Logic(different, FormulaLogicOperator.And,
            new Formula.Logic(degreeM, FormulaLogicOperator.And,
                new Formula.Logic(degreeN, FormulaLogicOperator.And, close)));
        return Disp(Seq(Exists, Sp, m, Comma, n, Comma, Sp, conditions));
    }
}
