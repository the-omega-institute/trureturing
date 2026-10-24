using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MultipartiteCHS;

internal sealed class ExtremalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict extrema of multipartite reciprocal coefficients at fixed order and size.",
        H("Multipartite coefficient extrema"),
        Blocks(
            Describe.Lean(DescribeId.Create("multipartite-esymm-cons"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal.esymm_cons"), H("Elementary symmetric sums after adjoining one entry"),
                StatementSource.FromAuthor(Disp(ConsIdentity())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Adjoining a natural-number entry to a multiset splits the next elementary symmetric sum into the old next sum and the new entry times the old preceding sum. The identity gives the two-entry coefficient expansion and the arithmetic of a positive integer family satisfying σ₃ = σₙ."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("multipartite-reciprocal-extrema"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal.recH_extremal"),
                H("Unique extremal part multisets"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix r at least two, n at least r, and a positive even degree 2m. Among all positive integer part sizes with sum n, the reciprocal coefficient is minimized by one part of size n minus r plus one and r minus one singleton parts. It is maximized by the balanced partition, whose part sizes differ by at most one. Equality at either endpoint forces the same part multiset, expressed by a permutation of the indices.")),
                    Paragraph(Text("Strong induction in the coefficient recurrence propagates elementary symmetric coefficient inequalities. A strict increase in the quadratic elementary coefficient forces a strict increase at every positive even degree, using positivity of the preceding even coefficient.")),
                    Paragraph(Text("For two selected part sizes x and y and remaining multiset c, the degree k plus two elementary coefficient is e[k+2](c) plus (x+y)e[k+1](c) plus xy e[k](c). A transfer preserving x+y and increasing xy weakly increases every elementary coefficient of degree at least two and strictly increases the quadratic coefficient.")),
                    Paragraph(Text("The admissible positive integer vectors form a finite set. Any maximizing vector must be equitable: otherwise a balancing transfer gives a strictly larger coefficient. The equitable-function characterization puts every part at the quotient n/r or one more; counting the larger parts produces a permutation of balancedParts. Any minimizing vector has at most one part larger than one: otherwise an unbalancing transfer gives a strictly smaller coefficient. Its remaining part is determined by the total sum.")),
                    Paragraph(Text("The recurrence comparison reuses recH_eq, recH_nonneg and recH_two_mul_pos. The multiset representation uses Finset.esymm_map_val, and the balanced classification uses Finset.equitableOn_iff and extension of an equivalence between the larger-part fibers. This theorem concerns recH; the separately proved spectral identity transfers it to CHS values."))),
                DescribeRole.Theorem))));

    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula ConsIdentity()
    {
        Formula x = F.Id("x"), s = F.Id("s"), k = F.Id("k");
        Formula multiset = Call("Multiset", Nats());
        Formula cons = Call("Multiset.cons", x, s);
        Formula next = Add(k, D(1));
        Formula left = Call("Multiset.esymm", cons, next);
        Formula right = Add(Call("Multiset.esymm", s, next),
            Mul(x, Call("Multiset.esymm", s, k)));
        return All(x, Nats(), All(s, multiset, All(k, Nats(), Equal(left, right))));
    }
}
