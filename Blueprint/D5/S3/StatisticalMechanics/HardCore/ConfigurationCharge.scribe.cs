using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class ConfigurationChargeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The occupation defect is the expectation of the exact signed configuration charge under one actual common-activity Gibbs law.",
        H("ConfigurationCharge"),
        Blocks(
            Paragraph(Text("The carrier is an arbitrary finite type, including the empty type. The graph is simple and the common real activity lambda is strictly positive. Configurations are all actual independent subsets, including the empty set. The existing GibbsOccupation law gives mass lambda to the power of the configuration cardinality divided by the actual partition sum. Every vertex weight and every expectation below use this same graph and activity. In the formulas, O(G,J,v), q(G,lambda,v), C(G,lambda,J) and D(G,lambda) denote occupiedNeighbors, degreeWeight, configurationCharge and occupationDefect. Z(G,lambda) is the sum of lambda to the cardinality of J over configurations(G,univ); M(G,lambda) is meanOccupation(G,univ,lambda), identified with the actual PMF expectation by GibbsOccupation.gibbs_expected_card.")),
            Describe.Lean(DescribeId.Create("hardcore-charge-occupied-neighbors"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.occupiedNeighbors"),
                H("Occupied neighbors"), StatementSource.FromAuthor(NeighborsFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The occupied neighbors of v are precisely the members of J adjacent to v, so their cardinality is the source random variable Y_v."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hardcore-charge-degree-weight"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.degreeWeight"),
                H("Common-activity degree weight"), StatementSource.FromAuthor(WeightFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weight q_v is lambda divided by 1 plus (degree(v) plus 1) times lambda; for positive lambda it is also the reciprocal of degree(v) plus 1 plus 1/lambda."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hardcore-charge-configuration-charge"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.configurationCharge"),
                H("Exact signed configuration charge"), StatementSource.FromAuthor(ChargeFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum over all v with at least two occupied neighbors of the sum of q_u over those occupied neighbors minus q_v. The charge is signed; neither it nor its expectation is asserted nonnegative."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hardcore-charge-occupation-defect"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.occupationDefect"),
                H("Actual occupation defect"), StatementSource.FromAuthor(DefectFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mean actual Gibbs configuration cardinality minus the sum of the degree weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hardcore-charge-defect-eq-expectation"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/ConfigurationCharge.defect_eq_expected_charge"),
                H("Actual Gibbs defect equals expected source charge"), StatementSource.FromAuthor(IdentityFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("This is the complete source identity: D equals the sum over actual independent configurations J of P(J) times C(J). The finite sum is also written using the existing actual Gibbs PMF. There is no local-balance certificate, assumed normalization, arbitrary marginal law, finite periodic proxy or nonempty-graph premise.")),
                    Paragraph(Text("The proof exchanges the sole occupied neighbor u of v with v. Independence supplies the reverse singleton-neighbor condition; the inverse exchange and equal cardinality preserve the common-activity weight. Opposite directed singleton contributions therefore cancel in expectation. The zero-neighbor contribution follows from the existing actual deletion partition identity and marked-weight identity. Finite double counting and the degree-weight denominator then give the exact defect. Empty carriers and edgeless graphs are included by the same finite sums.")),
                    Paragraph(Text("The configuration law, deletion partitions, occupation moments and finite PMF expectation all refer to the same independent-set family. The exchange acts on one configuration at a time and preserves its common-activity weight."))),
                DescribeRole.Theorem))));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Seq(F.Operatorname, F.Grp(F.Id(name))), [.. arguments]);
    private static Formula Rel(Formula a, FormulaRelationOperator relation, Formula b) =>
        new Formula.Relation(a, relation, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula SumOver(Formula index, Formula body) =>
        F.Seq(new Formula.Subscript(F.Sum, index), F.Sp, F.Open, body, F.Close);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Real() => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Parameters(Formula body, bool finite = false, bool equality = false)
    {
        Formula v = F.Id("V"), g = F.Id("G");
        body = All("G", Call("SimpleGraph", v), F.Seq(
            F.OpenBracket, Call("DecidableRel", Call("Adj", g)), F.CloseBracket,
            F.Comma, F.Sp, body));
        if (equality)
            body = F.Seq(F.OpenBracket, Call("DecidableEq", v), F.CloseBracket, F.Sp, body);
        if (finite)
            body = F.Seq(F.OpenBracket, Call("Fintype", v), F.CloseBracket, F.Sp, body);
        return All("V", F.Id("Type"), body);
    }
    private static Formula Q(Formula v) => Call("q", F.Id("G"), F.Id("lambda"), v);
    private static Formula O(Formula v) => Call("O", F.Id("G"), F.Id("J"), v);
    private static Formula NeighborsFormula() => F.Disp(Parameters(
        All("J", Call("Finset", F.Id("V")), All("v", F.Id("V"), Eq(O(F.Id("v")),
        F.Seq(F.OpenBrace, Mem(F.Id("u"), F.Id("J")), F.Mid,
            Call("Adj", F.Id("G"), F.Id("v"), F.Id("u")), F.CloseBrace))))));
    private static Formula WeightFormula() => F.Disp(Parameters(
        All("lambda", Real(), All("v", F.Id("V"), Eq(Q(F.Id("v")),
            new Formula.Fraction(F.Id("lambda"), Add(F.D(1), Mul(
                Add(Call("degree", F.Id("G"), F.Id("v")), F.D(1)), F.Id("lambda"))))))),
        finite: true));
    private static Formula ChargeFormula()
    {
        Formula v = F.Id("v"), u = F.Id("u");
        Formula index = F.Seq(Mem(v, F.Id("V")), F.Comma,
            Rel(F.D(2), FormulaRelationOperator.LessThanOrEqual, Call("card", O(v))));
        return F.Disp(Parameters(All("lambda", Real(), All("J", Call("Finset", F.Id("V")),
            Eq(Call("C", F.Id("G"), F.Id("lambda"), F.Id("J")),
                SumOver(index, Sub(SumOver(Mem(u, O(v)), Q(u)), Q(v)))))), finite: true));
    }
    private static Formula DefectFormula() => F.Disp(Parameters(All("lambda", Real(),
        Eq(Call("D", F.Id("G"), F.Id("lambda")),
            Sub(Call("M", F.Id("G"), F.Id("lambda")),
                SumOver(Mem(F.Id("v"), F.Id("V")), Q(F.Id("v")))))),
        finite: true, equality: true));
    private static Formula IdentityFormula()
    {
        Formula g = F.Id("G"), j = F.Id("J"), v = F.Id("V");
        Formula body = All("lambda", Real(), new Formula.Logic(
            Rel(F.D(0), FormulaRelationOperator.LessThan, F.Id("lambda")),
            FormulaLogicOperator.Implies,
            Eq(Call("D", g, F.Id("lambda")),
                SumOver(Mem(j, Call("configurations", g, Call("univ", v))),
                    Mul(new Formula.Fraction(new Formula.Power(F.Id("lambda"), Call("card", j)),
                        Call("Z", g, F.Id("lambda"))), Call("C", g, F.Id("lambda"), j))))));
        return F.Disp(All("V", F.Id("Type"), F.Seq(
            F.OpenBracket, Call("Fintype", v), F.CloseBracket, F.Sp,
            F.OpenBracket, Call("DecidableEq", v), F.CloseBracket, F.Comma, F.Sp,
            All("G", Call("SimpleGraph", v), F.Seq(
                F.OpenBracket, Call("DecidableRel", Call("Adj", g)), F.CloseBracket,
                F.Comma, F.Sp, body)))));
    }
}
