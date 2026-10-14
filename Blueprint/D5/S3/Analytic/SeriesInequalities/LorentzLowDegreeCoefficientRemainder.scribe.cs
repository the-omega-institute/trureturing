using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class LorentzLowDegreeCoefficientRemainderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/LorentzLowDegreeCoefficientRemainder.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Estimation/holtznazarovperes2011smoothcoins");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Bernstein arrays control the coefficient tails of centered Taylor truncations.",
        H("Bernstein Coefficient Tails of Taylor Polynomials"),
        Blocks(
            Paragraph(Text("Write B(d,c) for the polynomial with normalized Bernstein coefficients c "
                + "at degree d, T(P,p,r) for its Taylor polynomial through order r at p, and C(D,J,P) "
                + "for the degree-D Bernstein coefficient transform. The norm of a finite array is "
                + "its maximum coefficient modulus. These conventions include both endpoints.")),
            Entry("tail-bound", "taylor_coefficient_remainder_bound", "A uniform coefficient-tail estimate",
                TailFormula(false),
                "For every natural truncation order r, two constants A and K, both at least one, "
                + "work for every input degree d and output degree D satisfying A d at most D. "
                + "A complex disk bound obtained from the original coefficients is combined with "
                + "centered finite-population product moments. Summation of the resulting geometric "
                + "tail gives exponent (r+1)/2. No derivative bound on the input is assumed."),
            Entry("tail-array", "taylor_coefficient_remainder", "An actual Bernstein representation",
                TailFormula(true),
                "At each chosen output index J, the Taylor center is J/D. The corresponding "
                + "remainder has an actual degree-D coefficient array, whose Jth entry satisfies "
                + "the uniform estimate. The entire array vanishes when d is at most r. "
                + "The array can depend on J because its Taylor center does. This statement "
                + "concerns ordinary Taylor truncation in the large-ratio regime; the Lorentz "
                + "operator remainder is treated separately."))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula I(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(I(name), [.. args]);
    private static Formula Field(string name) => Seq(Mathbb, Grp(I(name)));
    private static Formula Arr(Formula n) => Seq(Call("Fin", Seq(n, Plus, D(1))), To, Sp, Field("C"));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Par(Formula x) => Seq(Open, x, Close);

    private static Formula TailFormula(bool array)
    {
        Formula r = I("r"), a = I("a"), d = I("d"), degree = I("D"), c = I("c"), j = I("J"), k = I("K"), scale = I("A");
        Formula polynomial = Call("B", d, c);
        Formula remainder = Seq(polynomial, Minus, Call("T", polynomial, Fr(j, degree), r));
        Formula bound = Seq(k, Cdot, Sp, Pow(Fr(d, degree), Fr(Seq(r, Plus, D(1)), D(2))), Cdot, Sp, Norm(c));
        Formula result = array
            ? Ex("a", Arr(degree), Seq(remainder, Eq, Call("B", degree, a), Land, Sp,
                Norm(Call("a", j)), Le, Sp, bound, Land, Sp,
                Par(Seq(d, Le, Sp, r, Rightarrow, Sp, a, Eq, D(0)))))
            : Seq(Norm(Call("C", degree, j, Par(remainder))), Le, Sp, bound);
        result = All("J", Field("N"), Seq(j, Le, Sp, degree, Rightarrow, Sp, result));
        result = All("c", Arr(d), result);
        result = All("d", Field("N"), All("D", Field("N"),
            Seq(D(0), Lt, Sp, d, Land, Sp, scale, Cdot, Sp, d, Le, Sp, degree, Rightarrow, Sp, result)));
        result = Ex("A", Field("R"), Ex("K", Field("R"),
            Seq(D(1), Le, Sp, scale, Land, Sp, D(1), Le, Sp, k, Land, Sp, result)));
        return Disp(All("r", Field("N"), result));
    }
}
