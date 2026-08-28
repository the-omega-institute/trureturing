using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Relabeling;

internal sealed class DifferentialEntropyChangeOfVariablesDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Relabeling/DifferentialEntropyChangeOfVariables."
            + "differential_entropy_change_of_variables";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Differential entropy changes by the expected logarithm of the absolute Jacobian.",
        H("Differential Entropy Change of Variables"),
        Blocks(Describe.Lean(
            DescribeId.Create("differential-entropy-change-of-variables"),
            DeclarationHandle.Create(Declaration),
            H("A differentiable equivalence contributes its log-Jacobian correction"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The carrier is the real vector space R^n. A nonnegative unit-mass density p, "
                        + "a differentiable equivalence f, its derivative A, and an everywhere-positive "
                        + "absolute determinant construct J(x) = |det A(x)| and the transformed density "
                        + "q(y) = p(f^{-1}(y))/J(f^{-1}(y)).")),
                Paragraph(Text(
                    "Integrability of p log p expresses finite source differential entropy. "
                        + "Integrability of p log J expresses finite absolute expected log-Jacobian. "
                        + "The transformed entropy integrand is integrable, and h(q) equals h(p) plus "
                        + "the density-weighted integral of log J.")),
                Paragraph(Text(
                    "If J is the positive constant c on the support of p, normalization makes the "
                        + "correction exactly log c. The qualitative observation that the correction "
                        + "usually depends on both the map and the distribution is not universalized.")),
                Paragraph(Text(
                    "The proof directly applies Mathlib's Jacobian change-of-variables theorem and its "
                        + "integrability equivalence. The remaining pointwise identity is log(p/J) = "
                        + "log p - log J, with the zero-density case handled separately."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Function(Formula variable, Formula body) =>
        Seq(Open, variable, Sp, Mapsto, Sp, body, Close);

    private static Formula Integral(Formula carrier, Formula variable, Formula integrand) =>
        Seq(Int, Underscore, Grp(carrier), Sp, Open, integrand, Close, Sp,
            F.Id("d"), variable);

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula f = F.Id("f");
        Formula derivative = F.Id("A");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula r = F.Id("r");
        Formula c = F.Id("c");
        Formula jacobian = F.Id("J");
        Formula transformed = F.Id("q");
        Formula entropy = F.Id("h");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula space = new Formula.Power(reals, n);
        Formula densityType = Seq(space, Sp, To, Sp, reals);
        Formula equivalenceType = Call("Equiv", space, space);
        Formula derivativeType = Seq(space, Sp, To, Sp,
            Call("ContinuousLinearMap", reals, space, space));
        Formula pAtX = Apply(p, x);
        Formula derivativeAtX = Apply(derivative, x);
        Formula jacobianAtX = Apply(jacobian, x);
        Formula transformedAtY = Apply(transformed, y);
        Formula logDensityAtX = Call("log", pAtX);
        Formula logJacobianAtX = Call("log", jacobianAtX);
        Formula jacobianDefinition = Seq(
            Lvert, Call("det", derivativeAtX), Rvert);
        Formula sourceIntegrand = Seq(pAtX, Sp, Cdot, Sp, logDensityAtX);
        Formula premiseCorrectionIntegrand = Seq(
            pAtX, Sp, Cdot, Sp, Call("log", jacobianDefinition));
        Formula correctionIntegrand = Seq(pAtX, Sp, Cdot, Sp, logJacobianAtX);
        Formula transformedIntegrand = Seq(
            transformedAtY, Sp, Cdot, Sp, Call("log", transformedAtY));
        Formula correctionIntegral = Integral(space, x, correctionIntegrand);
        Formula inverseAtY = Call("symm", f, y);
        Formula transformedDefinition = Seq(
            Frac, Grp(Apply(p, inverseAtY)), Grp(Apply(jacobian, inverseAtY)));
        Formula entropyDefinition = Seq(Minus, Integral(space, x,
            Seq(Apply(r, x), Sp, Cdot, Sp, Call("log", Apply(r, x)))));
        Formula letDefinitions = Seq(
            Operatorname, Grp(F.Id("let")), Open,
            Apply(jacobian, x), Sp, Colon, Eq, Sp, jacobianDefinition, Comma,
            RowBreak, Grp(),
            Apply(transformed, y), Sp, Colon, Eq, Sp, transformedDefinition, Comma,
            RowBreak, Grp(),
            Apply(entropy, r), Sp, Colon, Eq, Sp, entropyDefinition,
            Close, SemiSpace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, InMacro, Sp, naturals, Comma, Sp,
            p, Colon, Sp, densityType, Comma, RowBreak, Grp(),
            f, Colon, Sp, equivalenceType, Comma, Sp,
            derivative, Colon, Sp, derivativeType, Comma, RowBreak, Grp(),
            Open, Forall, Sp, x, InMacro, Sp, space, Comma, Sp,
            D(0), Sp, Leq, Sp, pAtX, Close, Sp, Land, RowBreak, Grp(),
            Integral(space, x, pAtX), Sp, Eq, Sp, D(1), Sp, Land,
            RowBreak, Grp(),
            Call("Integrable", Function(x, sourceIntegrand)), Sp, Land,
            RowBreak, Grp(),
            Call("Integrable", Function(x, premiseCorrectionIntegrand)), Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, x, InMacro, Sp, space, Comma, Sp,
            Call("HasFDerivAt", f, derivativeAtX, x), Close, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, x, InMacro, Sp, space, Comma, Sp,
            D(0), Sp, Lt, Sp, jacobianDefinition, Close,
            RowBreak, Grp(), Rightarrow, Sp,
            letDefinitions, RowBreak, Grp(),
            Call("Integrable", Function(y, transformedIntegrand)), Sp, Land,
            RowBreak, Grp(),
            Apply(entropy, transformed), Sp, Eq, Sp,
            Apply(entropy, p), Sp, Plus, Sp, correctionIntegral, Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, c, InMacro, Sp, reals, Comma, Sp,
            D(0), Sp, Lt, Sp, c, Sp, Rightarrow, Sp,
            Open, Forall, Sp, x, InMacro, Sp, Call("support", p), Comma, Sp,
            jacobianAtX, Sp, Eq, Sp, c, Close, Sp, Rightarrow, Sp,
            correctionIntegral, Sp, Eq, Sp, Call("log", c), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
