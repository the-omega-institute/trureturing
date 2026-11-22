using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHRootQuarterPhaseIncrementDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp forward increments of the full root spectrum under quarter-phase recurrence",
        H("Forward increments of the full root spectrum"),
        Blocks(Describe.Lean(DescribeId.Create("root-signal-quarter-phase-increment"),
            DeclarationHandle.Create(Owner + ".root_signal_quarter_phase_increment"),
            H("Uniform upper estimate and a signed late return"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Here S is the centered, normalized root signal summed over actual zero "
                    + "occurrences with analytic multiplicity. Put s(r) = 1/2 − 1/(2r). "
                    + "The displacement is rt for positive t.")),
                Paragraph(Text("The quarter phase q has value i on every distinct positive zeta zero. "
                    + "Its hull H is the closure of the phase orbit in the product topology. "
                    + "Positive occurrences use the same coordinate for each copy of a zero. "
                    + "Negative occurrences use the conjugate coordinate of the corresponding positive zero. "
                    + "Continuity carries the phase readout to arbitrarily late returns.")),
                Paragraph(Text("Under RH the leading coefficient of each occurrence is "
                    + "−r/(1/4 + γ²). The difference from the root coefficient is summable after "
                    + "multiplication by |γ|, so its contribution to the increment is bounded by "
                    + "a constant times t, uniformly in phase. At q the real parts sum to r times "
                    + "the positive-ordinate sine slope before dividing by s(r). This pairing "
                    + "uses the analytic multiplicity of each distinct zero. "),
                    Ref("D5/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness")),
                Paragraph(Text("The uniform upper estimate bounds the exponential increment by the "
                    + "absolute sine plus the cosine deficit. The absolute sine equals the sine "
                    + "of the absolute argument through |γ|t ≤ 1. The correction above that "
                    + "cutoff is controlled by the inverse-square tail. The origin cosine "
                    + "deficit contributes at the smaller scale t(1 + log(1/t)). "),
                    Ref("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp"),
                    Text(" "),
                    Ref("D5/S3/Weil/Mertens/ZeroAbscissaPower"))),
            DescribeRole.Theorem))));

    private static Formula R => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), R, body);
    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), R, body);

    private static Formula Statement()
    {
        var r = Id("r");
        var t = Id("t");
        var u = Id("u");
        var a = Id("A");
        var c = Id("C");
        var b = Id("b");
        var log = Call("log", new Formula.Fraction(Num(1), t));
        var increment = Subtract(Call("S", r, Add(u, Multiply(r, t))), Call("S", r, u));
        var leading = Multiply(
            new Formula.Fraction(Multiply(r, t), Multiply(Multiply(Num(2), F.Pi), Call("s", r))),
            new Formula.Power(log, Num(2)));
        var error = Multiply(Multiply(c, t), Add(Num(1), log));
        var upper = All("u", Le(new Formula.Absolute(increment), Add(leading, error)));
        var quarter = new Formula.Relation(Id("q"), FormulaRelationOperator.MemberOf, Id("H"));
        var returns = All("U", All("b", Imp(Lt(b, Subtract(leading, error)),
            Exists("u", And(Le(Id("U"), u), Lt(b, increment))))));
        var small = All("t", Imp(And(Lt(Num(0), t), Le(Multiply(a, t), Num(1))),
            And(upper, Imp(quarter, returns))));
        return F.Disp(Imp(Id("RH"), All("r", Imp(Lt(Num(1), r),
            Exists("A", Exists("C", And(Le(Num(2), a), And(Le(Num(0), c), small))))))));
    }
}
