using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHRootTailModulusDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootTailModulus";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The symmetric root-spectrum modulus on each tail",
        H("The logarithmic cusp on all tails"),
        Blocks(Describe.Lean(DescribeId.Create("root-signal-symmetric-tail-modulus"),
            DeclarationHandle.Create(Owner + ".root_signal_symmetric_tail_modulus"),
            H("The sharp two-term estimate for the tail supremum"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For the centered root spectrum S, let V(r,U,h) be the set of "
                    + "absolute values of S(r,u+h)+S(r,u−h)−2S(r,u) over u at least U. "
                    + "Set s(r)=1/2−1/(2r) and c=(Euler's constant−1+log(2π))/2. "
                    + "The spectrum keeps every actual zero occurrence with its multiplicity.")),
                Paragraph(Text("The symmetric difference factors each unit phase through "
                    + "2(cos(γh/r)−1). The root coefficient norm is at most r times "
                    + "the reciprocal-square weight. The nonnegative factor 1−cos "
                    + "then gives a summable majorant for the mode norms. After division "
                    + "by s(r), the sum of that majorant equals the cosine-kernel difference "
                    + "K(0)−K(h/r) scaled by 2r/s(r).")),
                Paragraph(Text("Recurrence puts values above every strict lower level of "
                    + "the origin difference in every tail. The supremum lies between "
                    + "that origin difference and the cosine majorant. Both have the "
                    + "same logarithmic and linear coefficients with quadratic errors. "
                    + "The estimate applies to symmetric differences."))),
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
        var u = Id("U");
        var h = Id("h");
        var cBound = Id("C");
        var set = Call("V", r, u, h);
        var leading = Multiply(new Formula.Fraction(h, Call("s", r)),
            Subtract(Add(Call("log", new Formula.Fraction(Num(1), h)), Call("log", r)),
                Multiply(Num(2), Id("c"))));
        var absoluteError = new Formula.Absolute(Subtract(Call("sup", set), leading));
        var estimate = Le(absoluteError, Multiply(cBound, Multiply(h, h)));
        var result = And(Call("Nonempty", set), And(Call("BddAbove", set), estimate));
        var increments = All("U", All("h", Imp(And(Lt(Num(0), h),
            Le(h, new Formula.Fraction(r, Num(2)))), result)));
        return F.Disp(Imp(Id("RH"), All("r", Imp(Lt(Num(1), r),
            Exists("C", And(Lt(Num(0), cBound), increments))))));
    }
}
