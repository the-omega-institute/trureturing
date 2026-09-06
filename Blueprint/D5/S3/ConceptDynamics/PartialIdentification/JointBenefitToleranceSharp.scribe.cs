using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class JointBenefitToleranceSharpDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/PartialIdentification/JointBenefitToleranceSharp.";
    private static Formula E10 => V("eta10");
    private static Formula E11 => V("eta11");
    private static Formula E20 => V("eta20");
    private static Formula E21 => V("eta21");
    private static Formula Hh => V("high");
    private static Formula Ll => V("low");
    private static Formula Zero => D(0);
    private static Formula One => D(1);
    private static Formula A => Call("benefitAmbiguityValue", E10, E11);
    private static Formula B => Call("benefitAmbiguityValue", E20, E21);
    private static Formula Value => Call("jointBenefitAmbiguityValue", E10, E11, E20, E21);
    private static Formula CloseModels => Call("JointMarginalTolerance", Hh, Ll, E10, E11, E20, E21);
    private static Formula Query(Formula model) => Call("jointMechanismBenefitMass", Call("markovianJointResponseMass", model));
    private static Formula Gap => Bin(Query(Hh), Minus, Query(Ll));
    private static Formula Marginal(string coordinate, string component, Formula model) =>
        Call(coordinate, Call("mass", Call(component, model)));
    private static Formula Closeness(string coordinate, string component, Formula tolerance) =>
        Bin(Abs(Bin(Marginal(coordinate, component, Hh), Minus, Marginal(coordinate, component, Ll))), Le, tolerance);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four intervention-marginal tolerances define a genuine bilinear comparison between two product-mechanism models. A three-corner envelope and original-carrier attaining models give its exact value.",
        H("Sharp two-mechanism joint-benefit robustness"),
        Blocks(
            Paragraph(Text("All scalar variables are rational. The variables high and low are the existing MarkovianJointMechanismModel values: each contains two independent complete response laws on Bool times Bool. Potential outcomes within an individual law may remain dependent. The comparison is across all marginal locations, not about one fixed observed center.")),
            Describe.Lean(DescribeId.Create("joint-marginal-tolerance"),
                DeclarationHandle.Create(Prefix + "JointMarginalTolerance"), H("Four actual marginal comparisons"),
                StatementSource.FromAuthor(Disp(All("high low eta10 eta11 eta20 eta21", Bin(CloseModels, Leftrightarrow, And(
                    Closeness("controlSuccessMarginal", "firstLaw", E10),
                    Closeness("treatmentSuccessMarginal", "firstLaw", E11),
                    Closeness("controlSuccessMarginal", "secondLaw", E20),
                    Closeness("treatmentSuccessMarginal", "secondLaw", E21)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("These four inequalities concern the original response-law readouts. The product restriction is in the original model semantics, not imposed by a new joint-coupling relaxation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-benefit-ambiguity-value"),
                DeclarationHandle.Create(Prefix + "jointBenefitAmbiguityValue"), H("Three competing configurations"),
                StatementSource.FromAuthor(Disp(All("eta10 eta11 eta20 eta21", Bin(Value, Eq,
                    Call("max", Call("max", A, B), Bin(One, Minus,
                        Bin(Bin(D(4), Cdot, Bin(One, Minus, A)), Cdot, Bin(One, Minus, B)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first two candidates place ambiguity in one mechanism and hold the other at certain benefit. The third places both upper mechanisms at certain benefit and simultaneously reduces both lower benefits."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("joint-benefit-tolerance-sharp"),
                DeclarationHandle.Create(Prefix + "joint_benefit_marginal_tolerance_sharp"), H("Global bound and attaining product models"),
                StatementSource.FromAuthor(Disp(All("eta10 eta11 eta20 eta21", Bin(
                    And(Bin(Zero, Le, E10), Bin(Zero, Le, E11), Bin(Zero, Le, E20), Bin(Zero, Le, E21)),
                    Rightarrow, And(
                        All("high low", Bin(CloseModels, Rightarrow, Bin(Abs(Gap), Le, Value))),
                        Exist("high low", And(CloseModels, Bin(Gap, Eq, Value)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The proof first derives the endpoint-sensitive inequality 2 times the upper benefit minus 2 times the single-mechanism ambiguity is at most the lower benefit. A slice-slope argument bounds the bilinear product difference at three corners.")),
                    Paragraph(Text("The first two corners reuse the existing one-mechanism sharpness theorem. The last corner uses explicitly normalized four-cell response laws. All four marginal tolerances and the actual joint-benefit query survive in the attaining pair.")),
                    Paragraph(Text("This is an exact subfamily within the broader multi-component optimization research direction. It is not a complete column-generation method, a theorem for shared disturbances, or a claim of literature-wide novelty."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("equal-total-tolerance-regimes"),
                DeclarationHandle.Create(Prefix + "equal_total_tolerance_regimes"), H("Equal-tolerance maximizing regime"),
                StatementSource.FromAuthor(Disp(All("eta10 eta11 eta20 eta21 s", Bin(
                    And(Bin(Zero, Le, V("s")), Bin(V("s"), Le, One),
                        Bin(Bin(E10, Plus, E11), Eq, V("s")), Bin(Bin(E20, Plus, E21), Eq, V("s"))),
                    Rightarrow, Bin(Value, Eq, Call("ite", Bin(V("s"), Le, Half(One)),
                        Half(Bin(One, Plus, V("s"))), Bin(Bin(D(2), Cdot, V("s")), Minus, Seq(V("s"), Caret, Grp(D(2)))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On 0 to 1, equal sums of the two within-mechanism tolerances yield (1+s)/2 through s=1/2, and 2s-s squared afterward. The algebraic formula needs the stated sum and s conditions; nonnegativity of each separate tolerance is supplied by the sharpness theorem when it is interpreted as a model guarantee."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Bin(Formula a, Formula op, Formula b) => Seq(Par(a), Sp, op, Sp, Par(b));
    private static Formula Abs(Formula value) => Seq(Lvert, value, Rvert);
    private static Formula Half(Formula value) => Seq(Frac, Grp(value), Grp(D(2)));
    // Preserve the source's right-associated conjunction tree.
    private static Formula And(params Formula[] items)
    {
        var result = items[^1];
        for (var i = items.Length - 2; i >= 0; --i) result = Bin(items[i], Land, result);
        return result;
    }
    private static Formula All(string names, Formula body) => Quant(Forall, names, body);
    private static Formula Exist(string names, Formula body) => Quant(Exists, names, body);
    private static Formula Quant(Formula symbol, string names, Formula body)
    {
        var parts = new List<Formula> { symbol, Sp };
        foreach (var name in names.Split(' ')) parts.AddRange([V(name), Comma, Sp]);
        parts.Add(body);
        return Seq([.. parts]);
    }
    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < arguments.Length; ++i)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(arguments[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
}
