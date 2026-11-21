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
                DescribeId.Create("on-line"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.on_line"),
                H("The real part of each actual zero under RH"),
                StatementSource.FromAuthor(OnLineClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the critical-line theorem to the zero selected by actualOccurrenceEquiv."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coeff-real"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.coeff_real"),
                H("The actual zero coefficient under RH"),
                StatementSource.FromAuthor(CoefficientClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here ofReal denotes the real embedding into the complex numbers. "
                    + "The critical-line identity gives the positive real denominator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coeff-norm-has-sum"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.coeff_norm_hasSum"),
                H("The complete coefficient norm series under RH"),
                StatementSource.FromAuthor(CoefficientMassClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under RH each coefficient's norm is its real part. "
                    + "Taking real parts in actualCoeff_hasSum gives the stated HasSum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("abs-g-sub-normalized-actual-h-le"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope.abs_G_sub_normalized_actualH_le"),
                H("The pointwise explicit-formula residual"),
                StatementSource.FromAuthor(ResidualClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact explicit formula splits G into the normalized real zero series and "
                    + "exp(-y/2)*(log(2*pi)-trivialT(y)). For positive y the triangle inequality "
                    + "and 0<=trivialT(y)<=1-log(2) give the displayed pointwise estimate."))),
                DescribeRole.Lemma),
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
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula UnderRh(Formula body) =>
        Disp(ImpliesClaim(Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))), body));

    private static Formula OnLineClaim()
    {
        var zero = Call("actualZero", F.Id("k"));
        return UnderRh(All("k", Nat, Equal(Call("Re", zero), new Formula.Fraction(D(1), D(2)))));
    }

    private static Formula CoefficientClaim()
    {
        var k = F.Id("k");
        var ordinate = Call("Im", Call("actualZero", k));
        var denominator = Add(new Formula.Fraction(D(1), D(4)), new Formula.Power(ordinate, D(2)));
        return UnderRh(All("k", Nat, Equal(Call("actualCoeff", k),
            Call("ofReal", new Formula.Fraction(D(1), denominator)))));
    }

    private static Formula CoefficientMassClaim()
    {
        var norm = new Formula.Norm(Call("actualCoeff", F.Id("k")));
        var series = Seq(LambdaLower, Sp, F.Id("k"), Sp, Colon, Sp, Nat, Comma, Sp, norm);
        return UnderRh(Call("HasSum", series, F.Id("firstLiMass")));
    }

    private static Formula GDefinition()
    {
        var y = F.Id("y");
        return Disp(All("y", Real, new Formula.Relation(Call("G", y),
            FormulaRelationOperator.Equal,
            Multiply(Call("exp", new Formula.Fraction(new Formula.Negate(y), D(2))),
                Call("U", Call("exp", y))))));
    }

    private static Formula ResidualClaim()
    {
        var y = F.Id("y");
        var scale = Call("exp", new Formula.Fraction(new Formula.Negate(y), D(2)));
        var normalized = Multiply(scale, Call("Re", Call("actualH", y)));
        var size = Add(new Formula.Absolute(Call("log", Multiply(D(2), F.Pi))),
            new Formula.Absolute(Subtract(D(1), Call("log", D(2)))));
        return Disp(All("y", Real, ImpliesClaim(Less(D(0), y),
            Le(new Formula.Absolute(Subtract(Call("G", y), normalized)), Multiply(scale, size)))));
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
        return UnderRh(And(envelope, recurrence));
    }
}
