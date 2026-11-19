using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSTwoSiteLocalRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteLocalRecovery";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local recovery from the normalized periodic two-site marginal",
        H("Local two-site recovery on the periodic chart"),
        Blocks(
            Definition("twoMass", "Squared amplitude mass",
                "The trace of the actual two-site Gram matrix sums the squared moduli of the periodic amplitudes. Its real part is the total mass."),
            Definition("normalizedTwo", "Normalized two-site marginal",
                "At positive mass, divide the Gram matrix of the two-site amplitude flattening by its trace. This gives the marginal of the unit-norm periodic state."),
            Describe.Lean(
                DescribeId.Create("periodic-mps-normalized-two-site-local-recovery"),
                DeclarationHandle.Create(Module + ".normalized_local_recovery"),
                H("A local decoder at each periodic length"),
                StatementSource.FromAuthor(Disp(RecoveryFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every ring length r+4 there is a fixed entry a and a nonempty open set of the four remaining complex chart coordinates. The periodic states have positive mass throughout this set, and the actual normalized two-site marginal is injective there. One decoder returns all four chart coordinates with a Lipschitz bound in the entrywise sup norm.")),
                    Paragraph(Text("Differentiating the identity that recovers the raw marginal from the mass and the normalized marginal makes every normalized kernel direction radial in the raw marginal. The nonsingular minor includes the raw value column and therefore forces that direction to vanish. A real linear left inverse of the normalized differential gives a fixed projection. The inverse function theorem on the projected observation gives the decoder. On a smaller neighborhood, the projected observation differs from the identity to first order with a uniform two-point error at most half the source distance. This gives the stated bound.")),
                    Paragraph(Text("The neighborhood is relative to the fixed chart. Phase classes represented elsewhere in the periodic state space are outside the uniqueness claim."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("periodic-mps-two-site-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula RecoveryFormula()
    {
        var complex = F.Id("Complex");
        var coordinates = new Formula.TypeArrow(Call("Fin", D(4)), complex);
        var bits = Call("Prod", Call("Fin", D(2)), Call("Fin", D(2)));
        var density = Call("Matrix", bits, bits, complex);
        var decoder = new Formula.TypeArrow(density, coordinates);
        var r = F.Id("r");
        var a = F.Id("a");
        var x = F.Id("x");
        var u = F.Id("U");
        var y = F.Id("y");
        var z = F.Id("z");
        var d = F.Id("decode");
        var l = F.Id("L");
        var tensors = Call("chart", a, y);
        var observation = Call("normalizedTwo", tensors, r);
        var map = Par(Seq(LambdaLower, Sp, Par(Seq(y, Colon, Sp, coordinates)), Sp, Mapsto, Sp, observation));
        var positive = Seq(D(0), Sp, Lt, Sp, Call("twoMass", tensors, r));
        var inverse = Seq(new Formula.Apply(d, [observation]), Sp, Eq, Sp, y);
        var changeInObservation = new Formula.Binary(observation, FormulaBinaryOperator.Subtract,
            Call("normalizedTwo", Call("chart", a, z), r));
        var changeInSource = new Formula.Binary(y, FormulaBinaryOperator.Subtract, z);
        var errorBound = Seq(Call("norm", changeInSource), Sp, Leq, Sp,
            new Formula.Binary(l, FormulaBinaryOperator.Multiply, Call("norm", changeInObservation)));
        var stability = Bind(FormulaQuantifier.ForAll, "y", coordinates, Implies(Member(y, u),
            Bind(FormulaQuantifier.ForAll, "z", coordinates, Implies(Member(z, u), errorBound))));
        var result = And(Call("IsOpen", u), Member(x, u),
            Bind(FormulaQuantifier.ForAll, "y", coordinates, Implies(Member(y, u), positive)),
            Call("InjOn", map, u),
            Bind(FormulaQuantifier.ForAll, "y", coordinates, Implies(Member(y, u), inverse)),
            Seq(D(0), Sp, Leq, Sp, l), stability);
        return Bind(FormulaQuantifier.ForAll, "r", F.Id("Nat"),
            Bind(FormulaQuantifier.Exists, "a", complex,
            Bind(FormulaQuantifier.Exists, "x", coordinates,
            Bind(FormulaQuantifier.Exists, "U", Call("Set", coordinates),
            Bind(FormulaQuantifier.Exists, "decode", decoder,
            Bind(FormulaQuantifier.Exists, "L", F.Id("Real"), result))))));
    }

    private static Formula Par(Formula body) => Seq(Open, body, Close);

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula Implies(Formula antecedent, Formula consequent) =>
        new Formula.Logic(Par(antecedent), FormulaLogicOperator.Implies, Par(consequent));

    private static Formula And(params Formula[] clauses) =>
        clauses.Reverse().Aggregate((right, left) => new Formula.Logic(Par(left), FormulaLogicOperator.And, Par(right)));

    private static Formula Bind(FormulaQuantifier q, string name, Formula type, Formula body) =>
        new Formula.Bind(q, FormulaIdentifier.Create(name), type, body);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
}
