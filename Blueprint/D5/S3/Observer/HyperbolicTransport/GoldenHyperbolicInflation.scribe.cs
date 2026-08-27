using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HyperbolicTransport;

internal sealed class GoldenHyperbolicInflationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden inflation expands the visible face and contracts the conjugate residual.",
        H("Golden Visible-Hidden Hyperbolic Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-visible-hidden-hyperbolic-transport"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HyperbolicTransport/GoldenHyperbolicInflation."
                        + "golden_visible_hidden_hyperbolic_transport"),
                H("Golden visible-hidden hyperbolic transport"),
                StatementSource.FromAuthor(TransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let epsilon_n denote endogenousResidualScale n. For every pair of "
                            + "real visible and hidden modules, the nth inflation step scales "
                            + "the visible coordinate by phi^n and the hidden coordinate by "
                            + "the nth power of the Galois conjugate phi-prime.")),
                    Paragraph(Text(
                        "The remaining four conjuncts identify epsilon_n with phi^(-n), "
                            + "identify the same value with |phi-prime|^n, and state that the "
                            + "one-step residual scale is positive and strictly below one. "
                            + "Thus the small parameter is the conjugate multiplier itself, "
                            + "not an independently supplied perturbation.")),
                    Paragraph(Text(
                        "At n=0 the scale is one, as required for zero iterations. The strict "
                            + "contraction assertion is attached to the one-step scale, so the "
                            + "zero-iteration case does not hollow out the theorem."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Scale/FibonacciEigen")),
        ]));

    private static Formula TransportFormula()
    {
        Formula visibleModule = F.Id("V");
        Formula hiddenModule = F.Id("H");
        Formula realModule = Seq(Operatorname, Grp(F.Id("Mod")), Underscore, Grp(Mathbb, Grp(F.Id("R"))));
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula phi = Varphi;
        Formula phiPrime = Seq(Varphi, Apos);
        Formula visible = new Formula.Subscript(x, F.Id("parallel"));
        Formula hidden = new Formula.Subscript(x, Perp);
        Formula epsilon = F.Id("epsilon");
        Formula epsilonN = new Formula.Subscript(epsilon, n);
        Formula epsilonOne = new Formula.Subscript(epsilon, D(1));
        Formula iterate = new Formula.Power(F.Id("goldenInflation"), n);
        Formula transported = Seq(iterate, Open, x, Close);
        Formula coordinatePair = Seq(
            Open,
            Multiply(new Formula.Power(phi, n), visible),
            Comma, Sp,
            Multiply(new Formula.Power(phiPrime, n), hidden),
            Close);
        Formula transport = Equal(transported, coordinatePair);
        Formula inverseGolden = Equal(
            epsilonN,
            new Formula.Power(phi, Seq(Minus, n)));
        Formula conjugateOrigin = Equal(
            epsilonN,
            new Formula.Power(new Formula.Absolute(phiPrime), n));
        Formula positiveScale = new Formula.Relation(
            D(0), FormulaRelationOperator.LessThan, epsilonOne);
        Formula strictContraction = new Formula.Relation(
            epsilonOne, FormulaRelationOperator.LessThan, D(1));

        Formula clauses = new Formula.Logic(
            transport,
            FormulaLogicOperator.And,
            new Formula.Logic(
                inverseGolden,
                FormulaLogicOperator.And,
                new Formula.Logic(
                    conjugateOrigin,
                    FormulaLogicOperator.And,
                    new Formula.Logic(
                        positiveScale,
                        FormulaLogicOperator.And,
                        strictContraction))));

        return Disp(Seq(
            Forall, Sp, visibleModule, Comma, Sp, hiddenModule,
            Sp, InMacro, Sp, realModule, Comma, Esc,
            Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Forall, Sp, x, Sp, InMacro, Sp,
            visibleModule, Sp, Times, Sp, hiddenModule, Comma, Esc,
            clauses, Dot));
    }
}
