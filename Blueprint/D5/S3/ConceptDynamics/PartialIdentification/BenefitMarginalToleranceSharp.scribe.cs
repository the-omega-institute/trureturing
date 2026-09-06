using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class BenefitMarginalToleranceSharpDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/PartialIdentification/BenefitMarginalToleranceSharp.";
    private static Formula Z => F.D(0);
    private static Formula One => F.D(1);
    private static Formula Eta0 => V("eta0");
    private static Formula Eta1 => V("eta1");
    private static Formula High => V("high");
    private static Formula Low => V("low");
    private static Formula Feature => Seq(Operatorname, Grp(V("benefitMomentFeature")));
    private static Formula Query => Seq(Operatorname, Grp(V("benefitMomentQuery")));
    private static Formula Value => Call("benefitAmbiguityValue", Eta0, Eta1);
    private static Formula Cert => Call("benefitToleranceCertificate", Eta0, Eta1);
    private static Formula Tolerance => P(Seq(LambdaLower, Sp, V("j"), Sp, Mapsto, Sp,
        Call("ite", R(V("j"), Eq, Z), Eta0, Eta1)));
    private static Formula Nonnegative => And(R(Z, Le, Eta0), R(Z, Le, Eta1));
    private static Formula Read(string name, Formula law) => Call(name, Call("mass", law));
    private static Formula Gap => R(Read("benefitResponseMass", High), Minus, Read("benefitResponseMass", Low));
    private static Formula CloseMoments => And(
        R(Abs(R(Read("controlSuccessMarginal", High), Minus, Read("controlSuccessMarginal", Low))), Le, Eta0),
        R(Abs(R(Read("treatmentSuccessMarginal", High), Minus, Read("treatmentSuccessMarginal", Low))), Le, Eta1));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every nonnegative rational tolerance pair, explicit causal response laws attain the largest possible benefit discrepancy, with a matching least residual certificate.",
        H("Sharp Boolean benefit ambiguity under marginal tolerances"),
        Blocks(
            Paragraph(Text("The array carrier is Fin 4 in response order 00,01,10,11; the two feature columns are indexed by Fin 2. All scalar entries and tolerances are rational. In the final theorem high and low are existing FiniteResponseLaw values on Bool times Bool, and all causal readouts are the existing source functions.")),
            Describe.Lean(DescribeId.Create("benefit-moment-feature"), DeclarationHandle.Create(Prefix + "benefitMomentFeature"), H("Actual potential-outcome indicator columns"),
                StatementSource.FromAuthor(Disp(R(Feature, Eq, Vector(Vector(Z, Z), Vector(Z, One), Vector(One, Z), Vector(One, One))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two columns encode control and treated success. The proof identifies their indexed expectations with controlSuccessMarginal and treatmentSuccessMarginal."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("benefit-moment-query"), DeclarationHandle.Create(Prefix + "benefitMomentQuery"), H("Benefit indicator"),
                StatementSource.FromAuthor(Disp(R(Query, Eq, Vector(Z, One, Z, Z)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This selects response 01 and is identified with benefitResponseMass on the original response-law carrier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("benefit-ambiguity-value"), DeclarationHandle.Create(Prefix + "benefitAmbiguityValue"), H("Closed ambiguity formula"),
                StatementSource.FromAuthor(Disp(All("eta0 eta1", R(Value, Eq, Call("min", One, Half(R(R(One, Plus, Eta0), Plus, Eta1))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The parameters bound differences between two models. They are not radii of confidence intervals about a fixed observation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("benefit-tolerance-certificate"), DeclarationHandle.Create(Prefix + "benefitToleranceCertificate"), H("Raw two-regime certificate"),
                StatementSource.FromAuthor(Disp(CertificateFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each record displays the high and low four-cell laws plus every envelope field. The first branch includes total tolerance one; the second saturates the probability range. No certificate validity or optimality fact is stored as a field."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("benefit-certificate-accepted"), DeclarationHandle.Create(Prefix + "benefitToleranceCertificate_accepted"), H("Acceptance for all nonnegative tolerances"),
                StatementSource.FromAuthor(Disp(All("eta0 eta1", R(Nonnegative, Rightarrow,
                    R(Call("checkContactCertificate", Feature, Query, Tolerance, Cert), Eq, V("true")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both parameter regimes are checked symbolically, including zeros, the boundary and tolerances larger than one. No optimizer or bounded sample set is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("benefit-certificate-budget"), DeclarationHandle.Create(Prefix + "benefitToleranceCertificate_budget"), H("Exact value of the certificate"),
                StatementSource.FromAuthor(Disp(All("eta0 eta1", R(Call("residualBudget", Tolerance, Call("envelope", Cert)), Eq, Value)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This algebraic equality holds for all rational parameters. Nonnegativity is needed separately for acceptance and the sharpness theorem."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("benefit-marginal-tolerance-sharp"), DeclarationHandle.Create(Prefix + "benefit_marginal_tolerance_sharp"), H("Universal bound, attaining causal pair and least dual value"),
                StatementSource.FromAuthor(Disp(All("eta0 eta1", R(Nonnegative, Rightarrow, And(
                    All("high low", R(CloseMoments, Rightarrow, R(Abs(Gap), Le, Value))),
                    ExistsOver("high low", And(CloseMoments, R(Gap, Eq, Value))),
                    Call("IsLeast", Call("residualBudgetValues", Feature, Query, Tolerance), Value)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first clause bounds every original-carrier pair. The second constructs normalized nonnegative original response laws attaining the oriented difference. The third certifies the least residual budget on the same four allowed cells. This is a global pairwise modulus over all marginal locations, not the identified interval at one fixed observed marginal vector."))), DescribeRole.Theorem))));

    private static Formula CertificateFormula()
    {
        var t = Half(R(R(One, Plus, Eta0), Plus, Eta1));
        var s = Half(R(R(One, Plus, Eta0), Minus, Eta1));
        var r = Call("min", One, Eta0);
        var first = Record(Vector(Z, t, R(One, Minus, t), Z), Vector(R(One, Minus, s), Z, Z, s),
            Vector(Seq(Minus, Half(One)), Half(One)), Half(One));
        var second = Record(Vector(Z, One, Z, Z), Vector(R(One, Minus, r), Z, Z, r), Vector(Z, Z), One);
        return All("eta0 eta1", R(Cert, Eq, Call("ite", R(R(Eta0, Plus, Eta1), Le, One), first, second)));
    }
    private static Formula Record(Formula high, Formula low, Formula beta, Formula upper) =>
        Seq(OpenBrace, R(V("high"), Eq, high), Comma, Sp, R(V("low"), Eq, low), Comma, Sp,
            R(V("envelope"), Eq, Seq(OpenBrace, R(V("offset"), Eq, Z), Comma, Sp,
                R(V("coefficient"), Eq, beta), Comma, Sp, R(V("lower"), Eq, Z), Comma, Sp,
                R(V("upper"), Eq, upper), CloseBrace)), CloseBrace);
    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula R(Formula x, Formula op, Formula y) => Seq(P(x), Sp, op, Sp, P(y));
    private static Formula Abs(Formula x) => Seq(Lvert, x, Rvert);
    private static Formula Half(Formula x) => Seq(Frac, Grp(x), Grp(F.D(2)));
    private static Formula All(string names, Formula body) => Quantify(Forall, names, body);
    private static Formula ExistsOver(string names, Formula body) => Quantify(Exists, names, body);
    private static Formula Quantify(Formula quantifier, string names, Formula body)
    {
        var items = new List<Formula> { quantifier, Sp };
        foreach (var name in names.Split(' ')) items.AddRange([V(name), Comma, Sp]);
        items.Add(body);
        return Seq([.. items]);
    }
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var k = 0; k < clauses.Length; k++)
        {
            if (k > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(P(clauses[k]));
        }
        return Seq([.. items]);
    }
    private static Formula Vector(params Formula[] values)
    {
        var items = new List<Formula> { OpenBracket };
        for (var k = 0; k < values.Length; k++)
        {
            if (k > 0) items.AddRange([Comma, Sp]);
            items.Add(values[k]);
        }
        items.Add(CloseBracket);
        return Seq([.. items]);
    }
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var k = 0; k < arguments.Length; k++)
        {
            if (k > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[k]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
