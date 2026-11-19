using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RHSharpActualEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual zero mass and arbitrarily late positive phase recurrence",
        H("The complete actual zero series under RH"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-g"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.G"),
                H("The normalized complete Mertens primitive"),
                StatementSource.FromAuthor(GDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real function U is CompleteMertensPeak.U, with the complete inclusive Mangoldt sum. The normalization is defined on every real y."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "Write M=ActualReciprocalSquareBounds.firstLiMass, and use the canonical actualZero, "
                + "actualCoeff and actualH of ActualZeroLaplace. Every natural index is an actual analytic "
                + "zero occurrence through actualOccurrenceEquiv, including its multiplicity. Both conjugate signs are included.")),
            Describe.Lean(
                DescribeId.Create("actual-g-control"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.actual_G_control"),
                H("Eventual absolute control and arbitrarily late values near the positive mass"),
                StatementSource.FromAuthor(ControlClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For G(y)=exp(-y/2)*U(exp y), the conclusion under RiemannHypothesis contains both: "
                        + "for each epsilon>0, eventually on all real y, abs(G(y))<M+epsilon; and for each "
                        + "epsilon>0 and real Y, a natural n exists with n>=Y and abs(G(n)-M)<epsilon.")),
                    Paragraph(Text(
                        "RH puts Re(actualZero(k))=1/2. Multiplication gives rho*(1-rho)=1/4+Im(rho)^2, "
                        + "so actualCoeff(k) is a positive real complex number and its norm is its real part. "
                        + "Apply Complex.hasSum_re to the canonical actualCoeff_hasSum: the complete norm mass "
                        + "is exactly M. Since norm(exp(y*rho))=exp(y/2), the triangle inequality for the "
                        + "absolutely summable full series gives norm(exp(-y/2)*actualH(y))<=M for every real y.")),
                    Paragraph(Text(
                        "On the compact infinite product group Z=(Nat -> Circle), put g(k)=Circle.exp(Im(rho(k))) "
                        + "and F(z)=tsum_k actualCoeff(k)*(z(k):Complex). Circle.exp uses exp(t*I), with no 2*pi. "
                        + "Each summand is continuous and has norm at most norm(actualCoeff(k)), independently "
                        + "of z. FunctionSeries.continuous_tsum therefore gives continuity on the entire product. "
                        + "The existing coefficient HasSum gives F(1)=M. Circle.coe_exp, pointwise powers and "
                        + "Complex.exp_nat_mul identify F(g^n)=exp(-n/2)*actualH(n) for every natural n. "
                        + "The identity is between complete summable series, by multiplication by one common scalar.")),
                    Paragraph(Text(
                        "Apply mapClusterPt_one_atTop_pow on this compact product, followed by "
                        + "MapClusterPt.continuousAt_comp and MapClusterPt.frequently. Every neighborhood of M "
                        + "contains F(g^n) for arbitrarily large natural n. This requires neither linear independence "
                        + "nor a rate or shrinking target.")),
                    Paragraph(Text(
                        "WholeFormula gives exactly G(y)=Re(exp(-y/2)*actualH(y))+residual(y) for y>0, "
                        + "where residual(y)=exp(-y/2)*(log(2*pi)-trivialT(y)). The complete trivial-zero bounds "
                        + "0<=trivialT(y)<=1-log(2) for y>=0 imply residual(y)->0. Complex.abs_re_le_norm "
                        + "controls the real phase error directly. Eventual control follows from the norm bound. "
                        + "For recurrence, combine a phase error below epsilon/2 with the residual below epsilon/2 "
                        + "and the required lower bound on n. The real-part estimate transfers the complex phase recurrence to G."))),
                DescribeRole.Theorem))));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesClaim(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula GDefinition()
    {
        var y = F.Id("y");
        return Disp(All("y", Real, new Formula.Relation(Call("G", y),
            FormulaRelationOperator.Equal,
            Multiply(Call("exp", new Formula.Fraction(new Formula.Negate(y), D(2))),
                Call("U", Call("exp", y))))));
    }

    private static Formula ControlClaim()
    {
        var e = F.Id("epsilon");
        var y = F.Id("y");
        var t = F.Id("T");
        var n = F.Id("n");
        var threshold = F.Id("Y");
        var mass = F.Id("firstLiMass");
        var envelope = All("epsilon", Real, ImpliesClaim(Less(D(0), e),
            ExistsOne("T", Real, All("y", Real, ImpliesClaim(Le(t, y),
                Less(new Formula.Absolute(Call("G", y)), Add(mass, e)))))));
        var recurrence = All("epsilon", Real, ImpliesClaim(Less(D(0), e),
            All("Y", Real, ExistsOne("n", Nat, And(Le(threshold, n),
                Less(new Formula.Absolute(Subtract(Call("G", n), mass)), e))))));
        return Disp(ImpliesClaim(Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))),
            And(envelope, recurrence)));
    }
}
