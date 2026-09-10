using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class SeparatorMediatorPricingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/SeparatorMediatorPricing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All separator branches are certified and reassembled into the original complete-mediator optimization.", H("SeparatorMediatorPricing"), Blocks(
            Paragraph(Text("M is finite with decidable equality. coupling is a normalized rational mediator-pair law; K is a Finset M. Branch variables range over the whole function type K to Bool. multiplier and probability map M to Q; threshold is rational. law and candidate are original FiniteResponseLaw values on M to Bool. Structure-field applications refer to the displayed raw certificate fields.")),
            Describe.Lean(DescribeId.Create("separator-pricing-certificate"), DeclarationHandle.Create(Prefix + "SeparatorPricingCertificate"),
                H("A total family of branch certificates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The raw fields are color : M to Bool; flows : (K to Bool) to STCutCertificate M; winner : K to Bool. The total function covers all 2^card(K) assignments. There is no proof-valued field and no producer-selected branch sublist."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("branch-value"), DeclarationHandle.Create(Prefix + "branchValue"),
                H("Price one branch in original units"), StatementSource.FromAuthor(Disp(All("M coupling K multiplier certificate branch", B(C("branchValue" , V("coupling"), V("K"), V("multiplier"), V("certificate"), V("branch")), Eq, B(C("branchOffset" , V("coupling"), V("K"), V("branch"), V("multiplier")), Plus, C("certifiedPricingValue" , C("residualCoupling" , V("coupling"), V("K")), C("color" , V("certificate")), C("branchMultiplier" , V("coupling"), V("K"), V("branch"), V("multiplier")), C("flows" , V("certificate"), V("branch")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The value includes the original fixed-coordinate offset and the checked residual price."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("check-separator-pricing"), DeclarationHandle.Create(Prefix + "checkSeparatorPricing"),
                H("Check all branches and the proposed winner"), StatementSource.FromAuthor(Disp(All("M coupling K multiplier certificate", B(C("checkSeparatorPricing" , V("coupling"), V("K"), V("multiplier"), V("certificate")), Eq, C("decide" , And(All("branch", B(C("checkBipartitePricing" , C("residualCoupling" , V("coupling"), V("K")), C("color" , V("certificate")), C("branchMultiplier" , V("coupling"), V("K"), V("branch"), V("multiplier")), C("flows" , V("certificate"), V("branch"))), Eq, V("true"))), All("branch", B(C("branchValue" , V("coupling"), V("K"), V("multiplier"), V("certificate"), V("branch")), Le, C("branchValue" , V("coupling"), V("K"), V("multiplier"), V("certificate"), C("winner" , V("certificate"))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both universal tests range over every function from K to Bool, including the unique assignment for empty K. Every branch uses the actual residual coupling and corrected multipliers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("winning-table"), DeclarationHandle.Create(Prefix + "winningTable"),
                H("Lift the winning cut to a causal response"), StatementSource.FromAuthor(Disp(All("M K certificate", B(C("winningTable" , V("K"), V("certificate")), Eq, C("clampTable" , V("K"), C("winner" , V("certificate")), C("flipTable" , C("color" , V("certificate")), C("side" , C("flows" , V("certificate"), C("winner" , V("certificate")))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected coordinates are restored after undoing the residual graph coloring. The result lies in the original full response-table carrier."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("check-separator-pricing-sound"), DeclarationHandle.Create(Prefix + "checkSeparatorPricing_sound"),
                H("An attained global maximum over all original columns"), StatementSource.FromAuthor(Disp(All("M coupling K multiplier certificate", B(B(C("checkSeparatorPricing" , V("coupling"), V("K"), V("multiplier"), V("certificate")), Eq, V("true")), Rightarrow, And(B(C("completeMediatorPricingScore" , V("coupling"), V("multiplier"), C("winningTable" , V("K"), V("certificate"))), Eq, C("branchValue" , V("coupling"), V("K"), V("multiplier"), V("certificate"), C("winner" , V("certificate")))), C("IsGreatest" , C("range" , C("completeMediatorPricingScore" , V("coupling"), V("multiplier"))), C("branchValue" , V("coupling"), V("K"), V("multiplier"), V("certificate"), C("winner" , V("certificate"))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each competitor is assigned to its own restriction on K. Its certified branch maximum is bounded by the proposed winner, so no unvisited original column can exceed the returned value."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("checked-separator-stopping-iff"), DeclarationHandle.Create(Prefix + "checked_separator_stopping_iff"),
                H("Exact full-family stopping test"), StatementSource.FromAuthor(Disp(All("M coupling K multiplier certificate threshold", B(B(C("checkSeparatorPricing" , V("coupling"), V("K"), V("multiplier"), V("certificate")), Eq, V("true")), Rightarrow, B(All("table", B(C("completeMediatorPricingScore" , V("coupling"), V("multiplier"), V("table")), Le, V("threshold"))), Leftrightarrow, B(C("branchValue" , V("coupling"), V("K"), V("multiplier"), V("certificate"), C("winner" , V("certificate"))), Le, V("threshold"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalization multiplier is compared to the certified maximum over all complete response columns, not only generated columns."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("checked-separator-causal-bound"), DeclarationHandle.Create(Prefix + "checked_separator_causal_bound"),
                H("Bound every law with the original marginal rows"), StatementSource.FromAuthor(Disp(All("M coupling K multiplier probability certificate law", B(And(B(C("checkSeparatorPricing" , V("coupling"), V("K"), V("multiplier"), V("certificate")), Eq, V("true")), All("i", B(C("linearObjective" , Lam("table", C("ite" , C("table" , V("i")), F.D(1), Z)), C("mass" , V("law"))), Eq, C("probability" , V("i"))))), Rightarrow, B(C("completeMediatorBenefit" , V("coupling"), V("law")), Le, B(C("branchValue" , V("coupling"), V("K"), V("multiplier"), V("certificate"), C("winner" , V("certificate"))), Plus, SumF("i", B(C("multiplier" , V("i")), Cdot, C("probability" , V("i")))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing expectation/dual bound is reused on the original coupling. This bound is valid before restricted-master optimality and does not require fair outcome marginals."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("checked-separator-master-is-greatest"), DeclarationHandle.Create(Prefix + "checked_separator_master_isGreatest"),
                H("Certify the original sharp upper endpoint"), StatementSource.FromAuthor(Disp(All("M coupling K multiplier probability certificate threshold candidate", B(And(B(C("checkSeparatorPricing" , V("coupling"), V("K"), V("multiplier"), V("certificate")), Eq, V("true")), B(C("branchValue" , V("coupling"), V("K"), V("multiplier"), V("certificate"), C("winner" , V("certificate"))), Le, V("threshold")), All("i", B(C("linearObjective" , Lam("table", C("ite" , C("table" , V("i")), F.D(1), Z)), C("mass" , V("candidate"))), Eq, C("probability" , V("i")))), B(C("completeMediatorBenefit" , V("coupling"), V("candidate")), Eq, B(V("threshold"), Plus, SumF("i", B(C("multiplier" , V("i")), Cdot, C("probability" , V("i"))))))), Rightarrow, C("IsGreatest" , C("setOf" , Lam("value", ExistsF("law", And(All("i", B(C("linearObjective" , Lam("table", C("ite" , C("table" , V("i")), F.D(1), Z)), C("mass" , V("law"))), Eq, C("probability" , V("i")))), B(C("completeMediatorBenefit" , V("coupling"), V("law")), Eq, V("value")))))), C("completeMediatorBenefit" , V("coupling"), V("candidate"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual normalized nonnegative candidate law, all original marginal rows, exact primal/dual equality and the checked global stop certify the full endpoint. The original mediator coupling stays fixed."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Z => F.D(0);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula B(Formula x, Formula op, Formula y) => Seq(P(x), Sp, op, Sp, P(y));
    private static Formula All(string names, Formula body) => Quantify(Forall, names, body);
    private static Formula Lam(string names, Formula body) => Quantify(LambdaLower, names, body);
    private static Formula ExistsF(string names, Formula body) => Quantify(Exists, names, body);
    private static Formula SumF(string name, Formula body) => Seq(F.Sum, Underscore, Grp(V(name)), Sp, P(body));
    private static Formula Quantify(Formula q, string names, Formula body)
    {
        var items = new List<Formula> { q, Sp };
        foreach (var name in names.Split(' ')) items.AddRange([V(name), Comma, Sp]);
        items.Add(body); return Seq([.. items]);
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
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var k = 0; k < args.Length; k++)
        {
            if (k > 0) items.AddRange([Comma, Sp]);
            items.Add(args[k]);
        }
        items.Add(Close); return Seq([.. items]);
    }
}
