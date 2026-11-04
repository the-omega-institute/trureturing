using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class WeightedFlatCertificateRefutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive flat-candidate gaps rule out dependency cycles and weighted certificates.",
        H("Acyclicity and weighted polynomial refutation"),
        Blocks(
            Paragraph(Text("A candidate relation C(a,b,c) records a distinguished opposite pair a and the two other pairs b and c. The directed dependency graph sends a to both b and c. A shared positive potential z satisfies z(a) >= 1 + z(b) + z(c) for every candidate, so every dependency edge strictly decreases z.")),
            Paragraph(Text("For a finite family of selected candidates, attach nonnegative weights with at least one positive weight. The weighted gap is the sum of each weight times z(a)-z(b)-z(c). The candidate inequalities and positivity force this gap to be strictly positive. A certificate asserting that the same gap is nonpositive therefore yields a contradiction, while the strict decrease independently excludes every directed cycle.")),
            Describe.Lean(
                DescribeId.Create("flat-candidate-cycle-and-certificate-refutation"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/WeightedFlatCertificateRefutation.flat_candidate_cycle_and_certificate_refutation"),
                H("Cycle exclusion and weighted certificate refutation"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The proof reuses the shared positive-length cycle theorem for the graph conclusion. It then sums the pointwise lower bounds for the weighted gaps; one strictly positive weight makes the sum of weights positive. The nonpositive certificate contradicts that strict lower bound.")),
                    Paragraph(Text("The result is an abstract finite certificate criterion. It does not assert that a particular geometric candidate exists, nor does it replace the separate derivation of the candidate inequalities from a realization."))),
                DescribeRole.Theorem)
        )));

    private static Formula Statement()
    {
        var qType = F.Id("Q");
        var sigmaType = F.Id("Sigma");
        var real = F.Id("Real");
        var prop = F.Id("Prop");
        var z = F.Id("z");
        var candidate = F.Id("C");
        var weights = F.Id("weights");
        var q = F.Id("q");
        var q1 = F.Id("q1");
        var q2 = F.Id("q2");
        var vector = Call("Function", qType, real);
        var candidateType = Call("Function", qType,
            Call("Function", qType, Call("Function", qType, prop)));
        var sigmaVector = Call("Function", sigmaType, qType);
        var positivity = All("v", qType, Lt(F.D(1), Call("z", F.Id("v"))));
        var candidateGap = All("a", qType,
            All("b", qType,
                All("c", qType,
                    Imp(Call("C", F.Id("a"), F.Id("b"), F.Id("c")),
                        Ge(Call("z", F.Id("a")),
                            Add(F.D(1), Add(Call("z", F.Id("b")), Call("z", F.Id("c")))))))));
        var weightNonneg = All("sigma", sigmaType,
            Le(F.D(0), Call("weights", F.Id("sigma"))));
        var weightSome = Exists("sigma", sigmaType,
            Lt(F.D(0), Call("weights", F.Id("sigma"))));
        var gap = Call("weightedGap", weights, z, q, q1, q2);
        var certificate = Le(gap, F.D(0));
        var selected = All("sigma", sigmaType,
            Call("C", Call("q", F.Id("sigma")), Call("q1", F.Id("sigma")), Call("q2", F.Id("sigma"))));
        var assumptions = And(positivity, candidateGap, weightNonneg, weightSome, certificate, selected);
        var cycle = Call("HasDirectedCycle", Call("candidateEdge", candidate));
        return All("Q", F.Id("Type"),
            All("Sigma", F.Id("Type"),
                All("z", vector,
                    All("C", candidateType,
                        All("weights", Call("Function", sigmaType, real),
                            All("q", sigmaVector,
                                All("q1", sigmaVector,
                                    All("q2", sigmaVector,
                                        Imp(assumptions,
                                            And(Neg(cycle), F.Id("False")))))))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula And(params Formula[] parts)
    {
        var result = parts[^1];
        for (var i = parts.Length - 2; i >= 0; i--)
            result = new Formula.Logic(parts[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Neg(Formula value) => new Formula.Negate(value);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Ge(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
}
