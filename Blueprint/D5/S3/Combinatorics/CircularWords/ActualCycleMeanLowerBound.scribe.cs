using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class ActualCycleMeanLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/ActualCycleMeanLowerBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The hidden carrier is exactly all legal cycles circles A, queries are the supported-label subtype A, and each response is actual deletion from the same original. Assume at least four labels, deterministic unit-cost observations, pointwise termination, and exact zero error.", H("Lower Cost for All Adaptive Circular Deletions"), Blocks(
            Paragraph(Text("The hidden carrier is exactly all legal cycles circles A, queries are the supported-label subtype A, and each response is actual deletion from the same original. Assume at least four labels, deterministic unit-cost observations, pointwise termination, and exact zero error.")),
            Describe.Lean(DescribeId.Create("distinct-paired"), DeclarationHandle.Create(Prefix + "distinct_paired"),
                H("Generic Partners Are Actual Double-Fibre Originals"), StatementSource.FromAuthor(Disp(Eq(Call("paired",F.Id("x"),F.Id("B"),F.Id("z")),Call("firstFibreOfAmbiguous",F.Id("x"),F.Id("B"),F.Id("z"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Identify the generic fibre(read A,carrier A,x,B) with FirstLift A x B using exact legal-carrier membership. A distinct second-label partner exists exactly when the actual two-entry candidateSet has cardinal at least two. R1 bounds it by two, so this is exactly cardinal two, the definition of ambiguous. This proves equality of the actual sets, rather than merely substituting m and r into an arithmetic inequality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-paired-bound"), DeclarationHandle.Create(Prefix + "actual_paired_bound"),
                H("All Second Queries Retain at Least Two Partners"), StatementSource.FromAuthor(Disp(Le(D(2),Call("card",Call("paired",F.Id("x"),F.Id("B"),F.Id("z")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every realized first fibre has exactly A.card-1 original cycles by deletion_fiber_card. If the second label differs, the set correspondence and the actual unique-double-fibre count give exactly two paired candidates. If it repeats the first label, all first-fibre answers coincide and every candidate has a distinct partner because A.card-1 is at least three. This covers every supported second query chosen by any adaptive history."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-history-lower-bound"), DeclarationHandle.Create(Prefix + "actual_history_lower_bound"),
                H("Every Exact Terminating Policy Obeys the Mean Bound"), StatementSource.FromAuthor(Disp(Le(Add(D(2),Div(D(2),Call("sub",Call("card",F.Id("A")),D(1)))),Call("uniformMeanTraceLength",F.Id("A"),F.Id("tr"))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let policy map the entire dependent observation history to a supported query or terminal label. For each legal original C, tr(C) and lab(C) are from some actual completed execution; no uniform stopping depth is given. Require a decoder of lab(C) to equal C. Nonempty A supplies Nonempty Q; the actual first-fibre size and paired-set bound discharge all generic hypotheses with m=A.card-1 and r=2. The unpruned finite-history bridge then gives mean trace length at least 2+2/(A.card-1), preserving repeated queries and arbitrary history dependence."))), DescribeRole.Theorem),
            Paragraph(Text("UniformCycleAttainment supplies a correct strategy querying pairwise-distinct supported x,z,y and the matching exact mean. A transient exact check combines its correctness and attainment with this lower theorem; the final conjunction is not a retained application wrapper. The proof uses the entire carrier with uniform prior and makes no finite-example substitution or assumed desired count.")))));

    private static Formula Call(string n, params Formula[] xs) => xs.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(n)), [.. xs]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
}
