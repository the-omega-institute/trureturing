using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSAmbiguityDensityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex-Zariski density of two-site collisions and sharp three-site recovery.",
        H("Sharp phase recovery on the periodic image"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-mps-actual-collision-density"),
                DeclarationHandle.Create(Module + ".actual_collision_polynomial_vanishing"),
                H("Polynomial vanishing on actual collisions"), StatementSource.FromAuthor(Disp(VanishingFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every r, every complex coordinate polynomial vanishing on all rank-four targets of nonproportional two-site collisions vanishes throughout the length r+4 trace-word image.")),
                    Paragraph(Text("The parity parameters give a nonempty ordinary open set of collisions. Unitary physical basis changes preserve the whole collision. Starting from this unitary invariance, singular value decomposition reduces polynomial continuation to varying two diagonal entries successively on the unit circle. Finite roots extend each entry to the complex plane.")),
                    Paragraph(Text("On a nonempty open set of shared pairs, change physical generators so that the second is traceless and its trace pairing with the first vanishes. The centered first matrix anticommutes with the second, which exchanges its two eigenlines. Rescaling their bases gives the diagonal and symmetric off-diagonal parity presentation. Trace is invariant under this virtual similarity. Polynomial continuation in all eight complex entries gives the full-image vanishing conclusion."))),
                DescribeRole.Theorem),
            Item("two_vs_three_phase_recovery", "Two-site ambiguity on every nonempty principal open",
                "Each nonempty principal complex-Zariski open contains a rank-four actual target with a nonproportional competitor of equal raw two-site density. At every rank-four target, equality of raw three-site density is equivalent to a unit-phase relation."),
            Item("three_site_recovery_principal_open", "A nonempty principal open for three-site recovery",
                "Fix a right inverse of a rank-four witness's flattening. The determinant of a variable flattening multiplied by that constant right inverse is a coordinate polynomial. At the witness it equals one, and on its nonvanishing locus the flattening has rank four, so the three-site phase theorem applies."),
            Item("normalize_two_site_collision", "Transport to the unit-mass slice",
                "The trace of the common raw two-site Gram is the positive squared mass. A common scaling of the shared cores by a length-root of the inverse square root of that mass makes the raw trace one. Both marginals remain equal and cancellation preserves the absence of a global scalar."))));

    private static DocumentBlock Item(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-mps-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula VanishingFormula()
    {
        var r = Id("r");
        var a = Id("A");
        var b = Id("B");
        var c = Id("c");
        var p = Id("P");
        var n = new Formula.Binary(r, FormulaBinaryOperator.Add, D(4));
        var core = new Formula.TypeArrow(Call("Fin", D(2)), Id("Bond"));
        var rank = Eq(Call("rank", Call("twoFlattening", a, r)), D(4));
        var raw = Eq(Call("rawTwo", b, r), Call("rawTwo", a, r));
        var nonphase = All("c", Id("Complex"), new Formula.Relation(Call("gamma", b, n, D(1)),
            FormulaRelationOperator.NotEqual, Call("smul", c, Call("gamma", a, n, D(1)))));
        var vanishes = Eq(Call("eval", Call("traceWord", D(2), D(2), n, a), p), D(0));
        var hypothesis = All("A", core, All("B", core, Imp(rank, Imp(raw, Imp(nonphase, vanishes)))));
        return All("r", Id("Nat"), All("P", Call("MvPolynomial", Call("Word", n), Id("Complex")),
            Imp(hypothesis, All("A", core, vanishes))));
    }

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
