using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.WeightedBond;

internal sealed class WeightedBondCompleteGraphSpecializationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/WeightedBond/CompleteGraphSpecialization.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/gonzalezdeleonwachs2026weighted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete-graph weighted bond polynomials.",
        H("Complete-graph weighted bond polynomials"),
        Blocks(
            Node("Mark",
                "The polynomial coefficient ring over the rationals.", DescribeRole.Definition),
            Node("reciprocalFactor",
                "The formal inverse of the finite factor rescaled by the parameter, with constant term one.", DescribeRole.Definition),
            Node("psiComplete_closed",
                "For positive n and r at least two, evaluate the literal finite-color rank polynomial by the first coefficient extraction below.", DescribeRole.Theorem),
            Node("reversePsi_closed",
                "For positive n and r at least two, evaluate the printed rank reversal by the second coefficient extraction below.", DescribeRole.Theorem),
            Node("reversePsi_at_zero",
                "For positive n and any r, the reversed polynomial at zero equals the degree-(n minus one) coefficient of the rank polynomial.", DescribeRole.Theorem),
            Node("result",
                "Here n+1 is the vertex count and q+2 is the number of colors. The formal variable of coefficient extraction is distinct from the polynomial indeterminate X. The two extractions give the source specialization and the printed rank-reversed polynomial. The last two equalities specify the reflection and its value at zero.", DescribeRole.Theorem, Evaluation())),
        []));

    private static DocumentBlock Node(string name, string prose, DescribeRole role, Formula? formula = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(name), formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Evaluation()
    {
        var n = F.Id("n");
        var q = F.Id("q");
        var x = F.Id("X");
        var vertices = Add(n, F.D(1));
        var colors = Add(q, F.D(2));
        var naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var markRing = F.Seq(F.Mathbb, F.Grp(F.Id("Q")), F.OpenBracket, x, F.CloseBracket);
        var exponential = Call("exp", markRing);
        var source = Call("sourceSpecialization", vertices, colors);
        var reversed = Call("reversePsi", vertices, colors);
        var factorial = F.Seq(n, F.Bang);
        Formula Coefficient(Formula rate, Formula marker) =>
            Multiply(factorial, Call("coeff", n,
                Multiply(Call("rescale", rate, exponential),
                    new Formula.Power(Call("reciprocalFactor", q, marker), vertices))));
        return F.Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), naturals,
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("q"), naturals,
                And(Equal(source, Coefficient(Subtract(F.D(1), Multiply(vertices, x)), x)),
                    And(Equal(reversed, Coefficient(Subtract(x, vertices), F.D(1))),
                        And(Equal(reversed, Call("reflect", n, source)),
                            Equal(Call("eval", F.D(0), reversed), Call("coeff", n, source))))))));
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
