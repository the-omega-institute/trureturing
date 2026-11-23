using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class DesignatedSummandThetaDissectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/yaqubi2026designatedsummands");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A parity bijection dissects the complete product U(q)U(q³).",
        H("The Jacobi parity dissection"),
        Blocks(
            Paragraph(Text("The three factors use the weighted Jacobi specialization, a sign twist on the Laurent support cone, and constant-unit evaluation. For the product U(q)U(q³), write the starting integer indices as a and b. The two affine coordinates come from a+3b and a−b divided by two. Folding one coordinate in each parity case gives the two disjoint lattices. The bijection preserves the degrees and turns the original signs into a positive even summand and a negative odd summand. The contributing index pairs at each fixed degree lie in a finite set.")),
            Node("prod_split_two", "A product through 2N consecutive indices is the product through the N even and the N odd indices.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("U", "The signed weighted Jacobi sum J at weight parameters 2 and 1, as a rational formal power series.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                UFormula()),
            Node("phi", "The bilateral theta series with square exponents. The defining specialization at weights 0 and 1 follows the Laurent twist with unit −1 and the identity coefficient map.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                PhiFormula()),
            Node("psi", "The unilateral theta series with triangular exponents. The defining Jacobi evaluation uses the identity coefficient map and the unit −1, with a constant factor of one half.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                PsiFormula()),
            Node("U_product", "The series U times the Euler factor f2 is f4 f1.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("phi_product", "The series phi times f1 squared and f4 squared is f2 to the fifth power.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("psi_product", "The series psi times f1 is f2 squared.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("U_dissection", "Over the rationals, U(q) U(q³) equals psi(q⁴) phi(q⁶) minus q phi(q²) psi(q¹²).", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string narrative, DescribeRole role, AssessedProvenance provenance, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("designatedsummandthetadissection-" + declaration.ToLowerInvariant().Replace('_', '-').Replace('₀', '0')),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(narrative))), role);

    private static Formula UFormula()
    {
        var index = F.Id("j");
        var sign = new Formula.Power(Parens(MinusOne()), F.Seq(F.Lvert, F.Sp, index, F.Rvert));
        var degree = F.Seq(F.D(2), new Formula.Power(index, F.D(2)), F.Sp, F.Minus, F.Sp, index);
        return Define(F.Id("U"), Call("J", F.D(2), F.D(1)),
            Sum(index, NumberSet("Z"), F.Seq(sign, F.Thin, new Formula.Power(F.Id("q"), degree))));
    }

    private static Formula PhiFormula()
    {
        var index = F.Id("j");
        var twisted = Call("map", Call("twist", F.Id("id"), MinusOne()), F.Id("jacobiSeries"));
        return Define(F.Varphi, Call("specialize", F.D(0), F.D(1), twisted),
            Sum(index, NumberSet("Z"), new Formula.Power(F.Id("q"), new Formula.Power(index, F.D(2)))));
    }

    private static Formula PsiFormula()
    {
        var index = F.Id("j");
        var half = new Formula.Fraction(F.D(1), F.D(2));
        var degree = new Formula.Fraction(F.Seq(index, Parens(F.Seq(index, F.Plus, F.D(1)))), F.D(2));
        return Define(F.Psi, F.Seq(half, F.Thin, Call("jacobiEvaluation", F.Id("id"), MinusOne())),
            Sum(index, NumberSet("N"), new Formula.Power(F.Id("q"), degree)));
    }

    private static Formula MinusOne() => F.Seq(F.Minus, F.D(1));
    private static Formula NumberSet(string symbol) => F.Seq(F.Mathbb, F.Grp(F.Id(symbol)));
    private static Formula Parens(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula Sum(Formula index, Formula domain, Formula body) =>
        F.Seq(new Formula.Subscript(F.Sum, F.Seq(index, F.Sp, F.InMacro, F.Sp, domain)), F.Sp, body);

    private static Formula Define(Formula left, Formula definingExpression, Formula series) =>
        F.Disp(F.Seq(left, F.Sp, F.Colon, F.Eq, F.Sp, definingExpression, F.Sp, F.Eq, F.Sp, series));
}
