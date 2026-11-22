using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHRootLateIncrementDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootLateIncrement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower scale for arbitrarily late root-spectrum increments",
        H("Root-spectrum increments at late starting points"),
        Blocks(Describe.Lean(DescribeId.Create("root-signal-late-increment-lower"),
            DeclarationHandle.Create(Owner + ".root_signal_late_increment_lower"),
            H("The logarithmic lower scale for forward increments"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("S(r,u) is the centered real root spectrum, with the full "
                    + "actual zero series counted with analytic multiplicity. The constants "
                    + "depend on the real root scale r. The starting point can depend on "
                    + "both the shift and the prescribed lower bound.")),
                Paragraph(Text("The logarithmic cusp makes the symmetric difference about "
                    + "zero positive at scale h log(1/h) for small positive h. "
                    + "The summable root coefficient majorant makes the shifted series "
                    + "a continuous function of the entire vector of unit phases.")),
                Paragraph(Text("The actual phase orbit returns arbitrarily late to every "
                    + "neighborhood of its initial vector. At such a return the continuous "
                    + "symmetric difference keeps a fixed fraction of its value at zero. "
                    + "It is the sum of one forward difference and the negative of the "
                    + "adjacent forward difference. At least one of their magnitudes "
                    + "is at least half the transported lower bound. Choose the time "
                    + "threshold so that both possible starts lie in the requested tail."))),
            DescribeRole.Theorem))));

    private static Formula Reals() => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Reals(), body);
    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), Reals(), body);

    private static Formula Statement()
    {
        var r = Id("r");
        var h = Id("h");
        var u = Id("u");
        var tail = Id("U");
        var threshold = Id("H");
        var lowerConstant = Id("d");
        var zero = Num(0);
        var one = Num(1);
        var increment = Subtract(Call("S", r, Add(u, h)), Call("S", r, u));
        var lower = Multiply(Multiply(lowerConstant, h),
            Call("log", new Formula.Fraction(one, h)));
        var late = All("U", Exists("u", And(Le(tail, u),
            Le(lower, new Formula.Absolute(increment)))));
        var small = All("h", Imp(And(Lt(zero, h), Lt(h, threshold)), late));
        var constants = Exists("d", And(Lt(zero, lowerConstant), Exists("H",
            And(And(Lt(zero, threshold), Lt(threshold, one)), small))));
        return F.Disp(Imp(Id("RH"), All("r", Imp(Lt(one, r), constants))));
    }
}
