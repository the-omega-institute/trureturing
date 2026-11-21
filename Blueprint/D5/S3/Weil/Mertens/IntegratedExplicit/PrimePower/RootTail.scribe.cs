using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower;

internal sealed class RootTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integrated Chebyshev tails at root cutoffs",
        H("Root substitution and the Costa Pereira remainder"),
        Blocks(
            Paragraph(Text("Write C(r,x) for the centered integral of (psi(t^(1/r))-t^(1/r))/t² over t>x, "
                + "scaled by the square root of x. Write J(r,x) for the corresponding uncentered integral. "
                + "Q(y) is the complete Chebyshev tail, W(r,y) is the integral of s^(-r)Q(s) over s>y, "
                + "and E(x) is Q(x)-Qtheta(x) minus the two unscaled uncentered integrals at r=2 and r=3.")),
            Describe.Lean(
                DescribeId.Create("centered-root-tail"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail.centered_root_tail"),
                H("The signed centered integral at a root cutoff"), StatementSource.FromAuthor(Centered()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At r=1 the centered integral is the complete tail Q(x) scaled by the square root of x. "
                    + "For r>1, substitute t=s^r with y=x^(1/r). The centered integral becomes "
                    + "r times the integral of the Chebyshev error kernel against s^(1-r), before scaling. "
                    + "The error kernel is -1/t below 1 and is integrable there above any positive cutoff. "
                    + "The triangular product of the absolute integrable Chebyshev kernel and "
                    + "s^(-r) on y<s<t is integrable. Fubini and the power primitive on y<s<t "
                    + "give the boundary term Q(y)y^(1-r) and the subtracted weighted integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("root-tail-main"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail.root_tail_main"),
                H("The explicit uncentered power contribution"), StatementSource.FromAuthor(MainTerm()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Chebyshev linear bound gives integrability for the uncentered "
                    + "root kernel. Integrating the subtracted power gives r/(r-1) times "
                    + "x^(1/r-1/2) after normalization by the square root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("root-cutoff-remainder"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RootTail.root_cutoff_remainder"),
                H("The integrated fifth-root majorant"), StatementSource.FromAuthor(Remainder()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Below 1 both Chebyshev functions vanish, so their centered kernels are "
                    + "integrable above any positive cutoff. The Costa Pereira inequalities in Mathlib retain the square and cube "
                    + "cutoffs in psi minus theta. The seventh-root term makes the remainder "
                    + "nonnegative. The uncentered fifth-root term is bounded by "
                    + "(log(4)+4)t^(1/5), which integrates against t^(-2) to "
                    + "(log(4)+4)(5/4)x^(-4/5) before normalization. The source inequality "
                    + "is reproduced in Broadbent et al., arXiv:2002.11068v2, equation (3.16)."))),
                DescribeRole.Theorem))));

    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Real, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Power(Formula x, Formula q) => F.Seq(x, F.Caret, F.Grp(q));
    private static Formula Rel(Formula l, FormulaRelationOperator op, Formula r) => new Formula.Relation(l, op, r);
    private static Formula Le(Formula l, Formula r) => Rel(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Lt(Formula l, Formula r) => Rel(l, FormulaRelationOperator.LessThan, r);
    private static Formula Eq(Formula l, Formula r) => Rel(l, FormulaRelationOperator.Equal, r);
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula And(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.And, r);

    private static Formula Centered()
    {
        var r = F.Id("r");
        var x = F.Id("x");
        var one = F.D(1);
        var y = Power(x, new Formula.Fraction(one, r));
        var right = Multiply(Multiply(r, Call("sqrt", x)),
            Subtract(Multiply(Call("Q", y), Power(F.Grp(y), Subtract(one, r))),
                Multiply(Subtract(r, one), Call("W", r, y))));
        return F.Disp(All("r", All("x", Imp(Le(one, r), Imp(Lt(F.D(0), x), Eq(Call("C", r, x), right))))));
    }

    private static Formula MainTerm()
    {
        var r = F.Id("r");
        var x = F.Id("x");
        var one = F.D(1);
        var main = Multiply(new Formula.Fraction(r, Subtract(r, one)),
            Power(x, Subtract(new Formula.Fraction(one, r), new Formula.Fraction(one, F.D(2)))));
        return F.Disp(All("r", All("x", Imp(Lt(one, r),
            Imp(Lt(F.D(0), x), Eq(Call("J", r, x), Add(main, Call("C", r, x))))))));
    }

    private static Formula Remainder()
    {
        var x = F.Id("x");
        var error = Call("E", x);
        var ten = F.Seq(F.D(1), F.D(0));
        var bound = Multiply(Multiply(Add(Call("log", F.D(4)), F.D(4)), new Formula.Fraction(F.D(5), F.D(4))),
            Power(x, new Formula.Negate(new Formula.Fraction(F.D(3), ten))));
        return F.Disp(All("x", Imp(Lt(F.D(0), x),
            And(Le(F.D(0), error), Le(Multiply(Call("sqrt", x), error), bound)))));
    }
}
