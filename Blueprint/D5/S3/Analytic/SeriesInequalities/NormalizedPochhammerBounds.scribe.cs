using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class NormalizedPochhammerBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/baezduarte2003criterion");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized complex Pochhammer products obey a uniform explicit disk bound.",
        H("Normalized Pochhammer Bounds"),
        Blocks(
            Entry("normalization", "normalizedPochhammer", "Factorial normalization",
                "Here P denotes normalizedPochhammer. The descending Pochhammer polynomial evaluated at z minus one is multiplied "
                + "by the kth power of minus one and divided by k factorial.", DescribeRole.Definition),
            Entry("product", "normalized_pochhammer_eq_prod", "The original finite product",
                "The normalization equals the product of one minus z divided by j plus one, "
                + "over j in the range from zero through k minus one. This identity retains "
                + "zero factors and all complex parameters.", DescribeRole.Theorem),
            Entry("zero", "normalized_pochhammer_zero", "The zero index",
                "At index zero the empty product is one. The compact-majorant consumer uses "
                + "this companion on its finite-prefix continuity path.", DescribeRole.Theorem),
            Entry("disk-bound", "normalized_pochhammer_norm_le", "An explicit disk bound",
                "For every nonnegative real radius R, every natural k at least one and every "
                + "complex z of norm at most R, the norm is at most exp(R + R squared) times "
                + "k raised to minus the real part of z. The proof accumulates squared factors "
                + "using the unrestricted scalar exponential inequality. Harmonic and finite "
                + "inverse-square bounds control the error without a sign restriction on the "
                + "real part. The explicit constant and closed disk are repo-derived refinements "
                + "of the source's unspecified open-disk constant, not a literal source statement. "
                + "These general analytic and algebraic results have utility kind none; they "
                + "are not bounded computations or certified finite instances.", DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        string commentary, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Statement(id)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(commentary))), role);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(FormulaDsl.Id(name), [.. args]);
    private static Formula P(Formula k, Formula z) => Call("P", k, z);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Q(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula All(string x, string type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x),
            Seq(Mathbb, Grp(FormulaDsl.Id(type))), body);
    private static Formula Statement(string id)
    {
        Formula k = FormulaDsl.Id("k"), z = FormulaDsl.Id("z"), r = FormulaDsl.Id("R"), j = FormulaDsl.Id("j");
        Formula p = P(k, z);
        Formula product = Seq(Prod, Underscore, Grp(j, InMacro, Sp, Call("range", k)),
            Seq(Open, D(1), Minus, Q(z, Seq(j, Plus, D(1))), Close));
        Formula body = id switch
        {
            "normalization" => Seq(p, Eq, Q(Seq(Pow(Seq(Open, Minus, D(1), Close), k), Sp,
                Call("eval", Call("descPochhammer", Seq(Mathbb, Grp(FormulaDsl.Id("C"))), k),
                    Seq(z, Minus, D(1)))), Seq(k, Bang))),
            "product" => Seq(p, Eq, product),
            "zero" => Seq(P(D(0), z), Eq, D(1)),
            "disk-bound" => Seq(D(0), Le, Sp, r, Land, Sp, D(1), Le, Sp, k, Land, Sp,
                new Formula.Norm(z), Le, Sp, r, Rightarrow, Sp, new Formula.Norm(p), Le, Sp,
                Call("exp", Seq(r, Plus, Pow(r, D(2)))), Sp,
                Pow(k, Seq(Minus, Call("Re", z)))),
            _ => throw new System.ArgumentException("Unknown statement", nameof(id))
        };
        body = All("z", "C", body);
        if (id != "zero") body = All("k", "N", body);
        if (id == "disk-bound") body = All("R", "R", body);
        return Disp(body);
    }
}
