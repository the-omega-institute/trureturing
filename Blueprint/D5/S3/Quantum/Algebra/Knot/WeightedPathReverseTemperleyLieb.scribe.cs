using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Knot;

internal sealed class WeightedPathReverseTemperleyLiebDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reversal of the actual fixed-endpoint legal paths supplies the missing reverse adjacent Temperley-Lieb relation.",
        H("Reverse Adjacent Law for Weighted Path Projections"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-path-reverse-temperley-lieb"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/Knot/WeightedPathReverseTemperleyLieb.weighted_path_reverse_temperley_lieb"),
            H("Reversing the two endpoint fibers"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let L be a finite decidable type, R a decidable symmetric relation, d strictly positive real vertex weights, and delta a strictly positive real number. Assume the Perron equality: for every a, the sum of d(b) over all b related to a is delta times d(a). For every n, both endpoints s and t, and every index with zero less than i and i+1 less than n, let P_i be the literal pathProjection of WeightedLegalPathTemperleyLieb on LegalPath R n s t. Then P_(i+1) P_i P_(i+1) is the complex square of delta inverse times P_(i+1). Empty endpoint fibers remain included; the index range is empty when n is less than three.")),
                Paragraph(Text("The existing supplier proves the forward adjacent law, P_i P_(i+1) P_i = delta inverse squared times P_i. Taking an adjoint repeats that same law and does not yield the reverse one. Instead, reverse every coordinate using Fin.rev. Symmetry of R makes the reversed sequence legal, exchanges s and t, and gives a genuine involutive equivalence of the two endpoint fibers.")),
                Paragraph(Text("Under this equivalence the literal local kernel at n-i pulls back to the kernel at i. The away-from-i guard is transported along the reverse coordinate bijection. The two flanks exchange places. On the support of the kernel those flank labels agree, so their weights and the denominator agree; no additional symmetry assumption on d is used. Off the support both entries are zero. Matrix.submatrix_mul_equiv transports the forward law at n-(i+1) on the reversed endpoint fiber into the required reverse law on the original fiber.")),
                Paragraph(Text("This is classical Temperley-Lieb path-model mathematics. Aharonov, Jones and Landau, A Polynomial Quantum Algorithm for Approximating the Jones Polynomial, arXiv:quant-ph/0511096v2, Definition 2.2 specifies both adjacent directions; Definition 3.2 and Claim 3.1 give the line-graph path representation. The present proof reuses the repository's arbitrary finite symmetric-relation supplier and its positive Perron data. Its endpoint reversal is a reusable algebraic coordinate equivalence, not a geometric reflection of knots.")),
                Paragraph(Text("The reverse relation fills an actual missing hypothesis for the subsequent Artin braid representation. Together with the existing idempotence and distant commutation laws it supplies both adjacent directions. This unit does not yet construct that representation, identify geometric braid closure or prove geometric Markov equivalence. It does not settle Laurent integrality, modular specialization, an explicit knot witness or the open knot target."))),
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
        Formula n = F.Id("n"), s = F.Id("s"), t = F.Id("t"), i = F.Id("i");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula p = Call("P", n, s, t, i);
        Formula q = Call("P", n, s, t, Seq(i, Plus, D(1)));
        Formula coefficient = Call("Pow", Call("Inv", F.Id("delta")), D(2));
        Formula law = All("n", nat, All("s", F.Id("L"), All("t", F.Id("L"), All("i", nat,
            Seq(Call("And", Call("Lt", D(0), i), Call("Lt", Seq(i, Plus, D(1)), n)), Rightarrow, Sp,
                EqTo(Mul(Mul(q, p), q), Call("SMul", coefficient, q)))))));
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Call("FiniteDecidable", F.Id("L")), Semi, Sp,
            Call("SymmetricPositivePerronData", F.Id("R"), F.Id("d"), F.Id("delta")),
            RowBreak, law, End, Grp(F.Id("gathered"))));
    }
}
