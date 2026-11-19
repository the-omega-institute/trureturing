using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSTwoSiteDifferentialDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteDifferential";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Differential rank of the actual two-site marginal on the periodic binary bond-two chart",
        H("Periodic two-site marginal differential"),
        Blocks(
            Definition("chart", "Affine chart",
                "The two symbol matrices are diag(a,b) and ((c,1),(d,e)). The chart fixes a and varies the real and imaginary parts of b,c,d,e."),
            Definition("rawTwo", "Actual two-site reduced density",
                "For length r+4, the amplitude flattening uses the existing periodic traceWord at every prefix and complement. Its product with its conjugate transpose is the unnormalized two-site partial trace."),
            Definition("augmented", "Radial column and real coordinate derivatives",
                "The value is the first column. The next eight columns are derivatives along the real and imaginary axes of b,c,d,e. Rows index all complex entries of the Hermitian marginal."),
            Describe.Lean(
                DescribeId.Create("periodic-mps-two-site-projective-rank-eight"),
                DeclarationHandle.Create(Module + ".projective_rank_eight"),
                H("Full projective differential rank at every length"),
                StatementSource.FromAuthor(Disp(RankFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every natural r the length r+4 admits a point of the displayed chart with a nonsingular nine-row minor. Complex independence of the value and the eight real derivative columns implies that the derivative has rank eight after quotienting out the real line of the value.")),
                    Paragraph(Text("Expanding the actual partial trace gives the trace of two Kronecker blocks followed by the complement transfer power. Evaluating Gaussian-integer polynomial lines in dual numbers retains the value and derivative and commutes with reduction modulo 13, where the imaginary unit maps to 5. The certificate verifies the selected minors by elimination and checks the base transfer identity at exponents 16 and 4 at four points. The square-zero ideal and characteristic 13 lift this to equality at exponents 164 and 8 for every direction.")),
                    Paragraph(Text("This differential result addresses local identifiability within the chart. Global exclusion of phase-inequivalent states with the same observed density remains a separate part of the periodic sharp-threshold question."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-mps-two-site-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula RankFormula()
    {
        var complex = F.Id("Complex");
        var bits = Call("Prod", Call("Fin", D(2)), Call("Fin", D(2)));
        var rows = new Formula.TypeArrow(Call("Fin", D(9)), Call("Prod", bits, bits));
        var x = new Formula.TypeArrow(Call("Fin", D(4)), complex);
        var minor = Call("submatrix", Call("augmented", F.Id("r"), F.Id("a"), F.Id("x")), F.Id("s"), F.Id("id"));
        var nonzero = Seq(Call("det", minor), Sp, Neq, Sp, D(0));
        return Bind(FormulaQuantifier.ForAll, "r", F.Id("Nat"),
            Bind(FormulaQuantifier.Exists, "a", complex,
            Bind(FormulaQuantifier.Exists, "x", x,
            Bind(FormulaQuantifier.Exists, "s", rows, nonzero))));
    }

    private static Formula Bind(FormulaQuantifier q, string name, Formula type, Formula body) =>
        new Formula.Bind(q, FormulaIdentifier.Create(name), type, body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
