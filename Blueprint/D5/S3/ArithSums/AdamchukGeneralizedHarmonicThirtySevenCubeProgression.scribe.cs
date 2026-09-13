using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class AdamchukGeneralizedHarmonicThirtySevenCubeProgressionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/adamchuk2007a116184");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every exponent in Adamchuk's progression gives a generalized harmonic numerator divisible by 37 cubed.",
        H("Adamchuk's A116184 progression"),
        Blocks(
            Node("H", "The generalized harmonic sum", HarmonicFormula(),
                "This is the generalized harmonic number H(36, n) of OEIS A116184; "
                    + "Rat.num below is the reduced numerator.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("adamchuk_a116184", "Cubic divisibility along the progression",
                DivisibilityFormula(),
                "Cubic nilpotence gives a third-order recurrence. Three initial "
                    + "certificates and induction make every recurrence value vanish, "
                    + "and the numerator bridge transfers that divisibility to the "
                    + "reduced numerator of the harmonic sum.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a116184-generalized-harmonic-thirty-seven-cube-progression"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a116184-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula HarmonicFormula()
    {
        var n = F.Id("n");
        var j = F.Id("j");
        var interval = QualifiedCall("Finset", "Icc", D(1), D(3, 6));
        var sum = Seq(
            new Formula.Subscript(Sum, Seq(j, Sp, InMacro, Sp, interval)),
            Sp,
            new Formula.Fraction(
                Cast(D(1), Rationals()),
                new Formula.Power(Cast(j, Rationals()), n)));
        var equation = new Formula.Relation(
            Call("H", n), FormulaRelationOperator.Equal, sum);
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            equation));
    }

    private static Formula DivisibilityFormula()
    {
        var k = F.Id("k");
        var exponent = new Formula.Binary(
            D(3),
            FormulaBinaryOperator.Add,
            new Formula.Binary(D(3, 6), FormulaBinaryOperator.Multiply, k));
        var modulus = Cast(new Formula.Power(D(3, 7), D(3)), Integers());
        var numerator = Call("num", Call("H", exponent));
        var divisibility = new Formula.Relation(
            modulus, FormulaRelationOperator.Divides, numerator);
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            Naturals(),
            divisibility));
    }

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));

    private static Formula Rationals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("Q")]));

    private static Formula Integers() => new Formula.Integers();
}
