using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Knot;

internal sealed class WeightedPathProjectionNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal old local projection is preserved by extension of a legal path, and the endpoint trace is cyclic.",
        H("Naturality of Weighted Path Projections"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-path-projection-naturality"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/WeightedPathProjectionNaturality.weighted_path_projection_naturality"),
            H("Old generators in the actual path tower"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let L be any finite decidable vertex type, R any relation on L, d any real vertex weights, and delta any real number. LegalPath, pathProjection, C, iota and tau are the actual declarations of WeightedLegalPathTemperleyLieb and WeightedPathMarkovTrace. The named kernel e(n,s,i) has endpoint block pathProjection R d delta n s t i; idempotence is not asserted for these arbitrary weights. Its index satisfies zero less than i less than n. Neither symmetry, positivity nor a Perron equality is needed for the two identities proved here; division and square root are the total Lean real operations.")),
                Paragraph(Text("Splitting a length n+1 path into its predecessor endpoint and length n prefix identifies each new endpoint fiber with the disjoint union of old fibers. The actual inclusion iota is block diagonal in these coordinates. Within a fixed predecessor block, appending an edge preserves every old coordinate and adds the same last coordinate to both paths, so the literal local kernel is unchanged. Between distinct predecessor blocks, the old local index i is strictly less than n; the kernel preserves coordinate n and consequently vanishes. These two entry calculations prove naturality of the full endpoint-block projection.")),
                Paragraph(Text("The trace tau is the weighted sum of the ordinary matrix traces, divided by delta to the n times d(s). Matrix trace cyclicity applies separately to each endpoint block, and the common weights and denominator preserve it. Empty endpoint fibers and n=0 remain in the trace scope. The generator condition zero less than i less than n is vacuous at n=0 and n=1.")),
                Paragraph(Text("This supplies the compatibility of old literal generators needed to extend path-model representations along the tower. The source theorem includes trace cyclicity by reuse of Matrix.trace_mul_comm. This is classical path-model background: Aharonov, Jones and Landau, A Polynomial Quantum Algorithm for Approximating the Jones Polynomial, arXiv:quant-ph/0511096v2, Definition 3.2 and equation (4) define the local path operator, while Definition 3.3 and Claim 3.6 describe the endpoint-weighted trace and its Markov properties for the line graph. The present statement covers arbitrary finite relation and weights; it is not attributed as their exact theorem.")),
                Paragraph(Text("The theorem does not construct an Artin braid group representation, a geometric closure map, geometric Markov equivalence or a knot invariant. It does not establish positivity or faithfulness of tau, Laurent polynomial integrality, modular specialization or an explicit knot witness."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula EqTo(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Statement()
    {
        Formula n = F.Id("n"), s = F.Id("s"), i = F.Id("i"), x = F.Id("X"), y = F.Id("Y");
        Formula e = Call("e", n, s, i), c = Call("C", n, s);
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula naturality = All("n", nat, All("s", F.Id("L"), All("i", nat,
                Seq(Call("And", Call("Lt", D(0), i), Call("Lt", i, n)), Rightarrow, Sp,
                EqTo(Call("iota", n, s, e), Call("e", Seq(n, Plus, D(1)), s, i))))));
        Formula cyclicity = All("n", nat, All("s", F.Id("L"), All("X", c, All("Y", c,
            EqTo(Call("tau", n, s, Mul(x, y)), Call("tau", n, s, Mul(y, x)))))));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Call("FiniteDecidable", F.Id("L")), Semi, Sp,
            Call("ArbitraryRelationAndRealWeights", F.Id("R"), F.Id("d"), F.Id("delta")),
            RowBreak, naturality, RowBreak, cyclicity,
            End, Grp(F.Id("gathered"))));
    }
}
