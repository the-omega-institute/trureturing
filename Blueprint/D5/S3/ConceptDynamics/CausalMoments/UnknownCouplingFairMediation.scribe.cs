using System.Collections.Generic;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class UnknownCouplingFairMediationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/UnknownCouplingFairMediation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Optimize both independent source laws exactly in the fair complete-mediation model with only mediator marginals supplied.", H("UnknownCouplingFairMediation"), Blocks(
            Paragraph(Text("M is an arbitrary finite type with decidable equality. control and treated are normalized rational FiniteResponseLaw values on M. coupling is a law on M times M; law is a law on complete tables M to Bool. HasMediatorMarginals and FairCompleteOutcome are the existing original causal predicates. Independent mechanisms and the no-direct-effect equation are built into completeMediatorBenefit. target is rational; table and best are Boolean functions on the whole M carrier.")),
            Describe.Lean(DescribeId.Create("partition-weight"), DeclarationHandle.Create(Prefix + "partitionWeight"),
                H("Combined selected mediator mass"), StatementSource.FromAuthor(Disp(All("M control treated table", B(C("partitionWeight", V("control"), V("treated"), V("table")), Eq, B(C("linearObjective", Lam("i", C("ite", C("table", V("i")), One, Z)), C("mass", V("control"))), Plus, C("linearObjective", Lam("i", C("ite", C("table", V("i")), One, Z)), C("mass", V("treated")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the sum of control(i)+treated(i) over the selected original mediator states. Its full-carrier total is two."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("partition-score"), DeclarationHandle.Create(Prefix + "partitionScore"),
                H("Crossing score of one partition"), StatementSource.FromAuthor(Disp(All("M control treated table", B(C("partitionScore", V("control"), V("treated"), V("table")), Eq, B(One, Minus, Abs(B(C("partitionWeight", V("control"), V("treated"), V("table")), Minus, One))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only the combined marginal weights enter this score. They do not specify an independent mediator coupling."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("mediator-cut-mass-le-partition-score"), DeclarationHandle.Create(Prefix + "mediatorCutMass_le_partitionScore"),
                H("Bound all compatible mediator couplings"), StatementSource.FromAuthor(Disp(All("M coupling control treated table", B(C("HasMediatorMarginals", V("coupling"), V("control"), V("treated")), Rightarrow, B(C("mediatorCutMass", V("coupling"), V("table")), Le, C("partitionScore", V("control"), V("treated"), V("table"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pointwise crossing indicator is bounded both by the sum of endpoint labels and by its complement. All original marginal equalities are retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-partition-attaining-coupling"), DeclarationHandle.Create(Prefix + "exists_partition_attaining_coupling"),
                H("Construct an attaining original mediator law"), StatementSource.FromAuthor(Disp(All("M control treated table", Ex("coupling", And(C("HasMediatorMarginals", V("coupling"), V("control"), V("treated")), B(C("mediatorCutMass", V("coupling"), V("table")), Eq, C("partitionScore", V("control"), V("treated"), V("table")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing Boolean Frechet law supplies a maximal-crossing coarse plan. The exact lift returns every individual original marginal and the same cut expectation, including null partitions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unknown-coupling-fair-interval"), DeclarationHandle.Create(Prefix + "unknown_coupling_fair_interval"),
                H("Complete identified interval with both laws unknown"), StatementSource.FromAuthor(Disp(All("M control treated", Ex("best", And(All("table", B(C("partitionScore", V("control"), V("treated"), V("table")), Le, C("partitionScore", V("control"), V("treated"), V("best")))), All("target", B(Ex("coupling law", And(C("HasMediatorMarginals", V("coupling"), V("control"), V("treated")), C("FairCompleteOutcome", V("law")), B(C("completeMediatorBenefit", V("coupling"), V("law")), Eq, V("target")))), Leftrightarrow, And(B(Z, Le, V("target")), B(V("target"), Le, Divide(C("partitionScore", V("control"), V("treated"), V("best")), F.D(2))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The optimal partition is obtained over the full finite carrier. One constructed mediator coupling already attains all intermediate targets through the existing fixed-coupling outcome-mixture theorem. No optimal coupling is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unknown-coupling-half-iff-partition"), DeclarationHandle.Create(Prefix + "unknown_coupling_half_iff_partition"),
                H("Exact one-half saturation criterion"), StatementSource.FromAuthor(Disp(All("M control treated", B(Ex("coupling law", And(C("HasMediatorMarginals", V("coupling"), V("control"), V("treated")), C("FairCompleteOutcome", V("law")), B(C("completeMediatorBenefit", V("coupling"), V("law")), Eq, Divide(One, F.D(2))))), Leftrightarrow, Ex("table", B(C("partitionWeight", V("control"), V("treated"), V("table")), Eq, One)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is an exact subset-partition condition on the combined mediator marginals. It is not a claim that generic nonfair or additionally restricted models have the same optimum."))), DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Z => F.D(0);
    private static Formula One => F.D(1);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula B(Formula x, Formula op, Formula y) => Seq(P(x), Sp, op, Sp, P(y));
    private static Formula All(string names, Formula body) => Quantify(Forall, names, body);
    private static Formula Ex(string names, Formula body) => Quantify(Exists, names, body);
    private static Formula Lam(string names, Formula body) => Quantify(LambdaLower, names, body);
    private static Formula Abs(Formula x) => Seq(Lvert, x, Rvert);
    private static Formula Divide(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula Quantify(Formula q, string names, Formula body)
    {
        var xs = new List<Formula> { q, Sp };
        foreach (var name in names.Split(' ')) xs.AddRange([V(name), Comma, Sp]);
        xs.Add(body); return Seq([.. xs]);
    }
    private static Formula And(params Formula[] values)
    {
        var xs = new List<Formula>();
        for (var i = 0; i < values.Length; i++)
        { if (i > 0) xs.AddRange([Sp, Land, Sp]); xs.Add(P(values[i])); }
        return Seq([.. xs]);
    }
    private static Formula C(string name, params Formula[] values)
    {
        var xs = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < values.Length; i++)
        { if (i > 0) xs.AddRange([Comma, Sp]); xs.Add(values[i]); }
        xs.Add(Close); return Seq([.. xs]);
    }
}
