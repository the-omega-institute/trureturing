using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class RationalGroupMatrixCutoffDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/RationalGroupMatrixCutoff.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => And(Implies(a, b), Implies(b, a));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Id(string name) => F.Id(name);
    private static Formula.BoundVariable[] GroupData => [
        B("H", Id("Type")), B("groupH", Call("Group", Id("H"))),
        B("finiteH", Call("Fintype", Id("H"))), B("n", Id("Nat"))];
    private static Formula GroupMat => Call("GroupMat", Id("H"), Id("n"), Id("n"));
    private static Formula Decomposition => Call("RationalDecomposition", Id("H"));
    private static Formula BlocksClaim => All(Iff(Call("UniformMatrix", Id("C")),
        All(Equal(Call("block", Id("W"), Id("l"), Id("C")), D(0)),
            B("l", Call("Fin", Call("count", Id("W")))))),
        [.. GroupData, B("W", Decomposition), B("C", GroupMat)]);
    private static Formula CutoffClaim => All(Le(Call("tau", Id("A")),
        Call("finiteWithTop", Call("multiply", Id("n"), Call("bH", Id("W"))))),
        [.. GroupData, B("W", Decomposition), B("positiveN", Call("NatPositive", Id("n"))),
         B("A", GroupMat), B("uniformizes", Call("Uniformizes", Id("A")))]);
    private static Formula RationalClaim => All(Equal(Call("rationalEntry", Id("C"), Id("i"), Id("j")),
        Call("scalarMultiply", Call("castRat", Call("augmentationEntry", Id("C"), Id("i"), Id("j"))),
            Call("average", Id("H")))),
        [.. GroupData, B("C", GroupMat), B("uniform", Call("UniformMatrix", Id("C"))),
         B("i", Call("Fin", Id("n"))), B("j", Call("Fin", Id("n")))]);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original rational matrix orders give the cutoff n times b_H over the same division algebras.",
        H("The rational Wedderburn cutoff"), Blocks(
            Describe.Lean(DescribeId.Create("uniform-natural-matrix-block-kernel"),
                DeclarationHandle.Create(Prefix + "uniform_iff_blocks_zero"), H("Actual uniformity and faithful blocks"),
                StatementSource.FromAuthor(Disp(BlocksClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("W is an actual augmentation-first rational decomposition with positive factor count, positive matrix orders r_l and finite rational division algebras D_l. The map block(W,l,C) casts natural coefficients to rational coefficients, applies the l-th tail factor entrywise, then flattens Mat(n,Mat(r_l,D_l)) to Mat(Fin(n) times Fin(r_l),D_l). Faithfulness and augmentation-firstness identify its simultaneous zero kernel with uniform coefficients. This is a theorem about every C, not an assumed bridge for selected powers."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("least-positive-rational-cutoff"),
                DeclarationHandle.Create(Prefix + "tau_le_cutoff"), H("The exact bound n*b_H"),
                StatementSource.FromAuthor(Disp(CutoffClaim)), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The natural number bH(W) is the maximum of W's original nontrivial rational matrix orders r_l. A positive uniform power makes every tail block nilpotent. Right multiplication on row vectors is linear over the same division ring and reverses products, but preserves powers of one matrix. Kernel stabilization therefore kills an n*r_l dimensional block by exponent n*r_l, and hence all blocks vanish by n*bH(W).")),
                    Paragraph(Text("The dimension is measured over D_l, not over the rationals; there is no factor dim_Q(D_l). The hypotheses n>0, positive factor count and positive r_l ensure that n*bH(W) is a positive exponent, as required by the least-positive convention. The trivial group uses the separate tau=1 boundary and has no artificial b_H."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("natural-uniform-rational-formula"),
                DeclarationHandle.Create(Prefix + "uniform_rational_expression"), H("Rational expression of a natural uniform matrix"),
                StatementSource.FromAuthor(Disp(RationalClaim)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("rationalEntry(C,i,j) is the natural entry C[i,j] with its coefficients cast to the rationals; augmentationEntry is the natural augmentation entry. The equality is entrywise equality in Q[H]. It divides only after casting to the rationals and does not assert divisibility by introducing an operation in the natural semiring."))), DescribeRole.Theorem))));
}
