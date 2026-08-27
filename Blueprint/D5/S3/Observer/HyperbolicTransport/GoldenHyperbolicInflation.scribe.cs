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
                        "The ambient carrier is the source six-dimensional real space. Phi, "
                            + "P_parallel, and P_perp are supplied operators: the two projections "
                            + "are complementary, commute with Phi, have rank-three images, and "
                            + "satisfy the stated expanding and contracting spectral equations.")),
                    Paragraph(Text(
                        "Writing q_parallel and q_perp for the two projection readouts, induction "
                            + "on n proves that q_parallel(Phi^n x) and q_perp(Phi^n x) acquire "
                            + "the factors phi^n and (phi-prime)^n. The transport law is therefore "
                            + "a consequence of the hypotheses on the given Phi, not the reduction "
                            + "of a coordinatewise-defined inflation function.")),
                    Paragraph(Text(
                        "FibonacciEigen supplies contracting_eigenvalue_eq_goldenConj. Together "
                            + "with the pinned real golden-ratio identities, it identifies "
                            + "epsilon_n with both phi^(-n) and |phi-prime|^n and proves that the "
                            + "one-step scale lies strictly between zero and one."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S1/Scale/FibonacciEigen")),
        ]));

    private static Formula TransportFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula ambient = new Formula.Power(real, D(6));
        Formula endomorphism = Seq(
            Operatorname, Grp(F.Id("End")), Underscore, Grp(real), Open, ambient, Close);
        Formula pParallel = new Formula.Subscript(F.Id("P"), F.Id("parallel"));
        Formula pPerp = new Formula.Subscript(F.Id("P"), Perp);
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula sourcePhi = F.Id("Phi");
        Formula phi = Varphi;
        Formula phiPrime = Seq(Varphi, Apos);
        Formula epsilon = F.Id("epsilon");
        Formula epsilonN = new Formula.Subscript(epsilon, n);
        Formula epsilonOne = new Formula.Subscript(epsilon, D(1));
        Formula phiIterate = Seq(new Formula.Power(sourcePhi, n), Open, x, Close);
        Formula parallelTransport = Equal(
            Seq(pParallel, Open, phiIterate, Close),
            Multiply(new Formula.Power(phi, n), Seq(pParallel, Open, x, Close)));
        Formula perpendicularTransport = Equal(
            Seq(pPerp, Open, phiIterate, Close),
            Multiply(new Formula.Power(phiPrime, n), Seq(pPerp, Open, x, Close)));
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

        Formula conclusions = new Formula.Logic(
            parallelTransport,
            FormulaLogicOperator.And,
            new Formula.Logic(
                perpendicularTransport,
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
                            strictContraction)))));

        Formula hypotheses = Seq(
            sourcePhi, Sp, Circ, Sp, pParallel, Sp, Eq, Sp,
              Multiply(phi, pParallel), Sp, Land, Sp,
            sourcePhi, Sp, Circ, Sp, pPerp, Sp, Eq, Sp,
              Multiply(phiPrime, pPerp), Sp, Land, Sp,
            pParallel, Sp, Circ, Sp, pParallel, Sp, Eq, Sp, pParallel, Sp, Land, Sp,
            pPerp, Sp, Circ, Sp, pPerp, Sp, Eq, Sp, pPerp, Sp, Land, Sp,
            pParallel, Sp, Circ, Sp, pPerp, Sp, Eq, Sp, D(0), Sp, Land, Sp,
            pParallel, Sp, Plus, Sp, pPerp, Sp, Eq, Sp, F.Id("I"), Sp, Land, Sp,
            pParallel, Sp, Circ, Sp, sourcePhi, Sp, Eq, Sp,
              sourcePhi, Sp, Circ, Sp, pParallel, Sp, Land, Sp,
            pPerp, Sp, Circ, Sp, sourcePhi, Sp, Eq, Sp,
              sourcePhi, Sp, Circ, Sp, pPerp, Sp, Land, Sp,
            Call("finrank", Call("range", pParallel)), Sp, Eq, Sp, D(3), Sp, Land, Sp,
            Call("finrank", Call("range", pPerp)), Sp, Eq, Sp, D(3));

        Formula quantifiedConclusion = Seq(
            Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            Forall, Sp, x, Sp, InMacro, Sp, ambient, Comma, Esc,
            conclusions, Dot);

        return Disp(Seq(
            Forall, Sp, sourcePhi, Comma, Sp, pParallel, Comma, Sp, pPerp,
            Sp, InMacro, Sp, endomorphism, Comma, Esc,
            new Formula.Logic(hypotheses, FormulaLogicOperator.Implies, quantifiedConclusion)));
    }
}
