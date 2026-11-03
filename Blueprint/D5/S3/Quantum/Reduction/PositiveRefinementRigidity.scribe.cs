using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Reduction;

internal sealed class PositiveRefinementRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive domination by identity determines one scalar on all orthogonal projections.",
        H("Positive refinement rigidity"),
        Blocks(
            Paragraph(Text("Let Phi be a complex linear endomorphism of the matrices on an arbitrary finite coordinate type. Assume positivity on every positive semidefinite input and the Loewner inequality Phi(X) less than or equal to X on those same inputs. Complete positivity and a Kraus representation are not hypotheses. A chosen coordinate certifies that the matrix algebra is nonzero.")),
            Describe.Lean(
                DescribeId.Create("identity-dominated-projection-scalar"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/PositiveRefinementRigidity.identity_dominated_projection_scalar"),
                H("A common scalar for every projection"),
                StatementSource.FromAuthor(ProjectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There is a real scalar c between zero and one such that Phi(I) is cI and Phi(P) is cP for every Hermitian idempotent P. The scalar is the chosen diagonal entry of Phi(I). Zero projections and one dimensional algebras are included.")),
                    Paragraph(Text("For a projection P, positivity and domination put Phi(P) in the corner of P and Phi(I minus P) in its orthogonal corner. Their sum is Phi(I), which therefore commutes with P and has Phi(P) as its compression. Coordinate projections make Phi(I) diagonal. The projection onto the sum of any two distinct coordinate vectors equates the corresponding diagonal entries. Positivity of Phi(I) and I minus Phi(I) bounds the common entry.")),
                    Paragraph(Text("This projection conclusion is an intermediate consequence for positive refinements of a canonical filter. Transferring it to arbitrary complex matrices, singular effects, unequal direct sums, all original finite record branches, and their complete positivity requires the corresponding matrix-span and support bridges. No assertion about an unrelated coarse completely positive map follows from this projection statement."))),
                DescribeRole.Theorem))));

    private static Formula At(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Adj(Formula x) => Seq(x, Caret, Grp(Star));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Inst(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket, Sp);
    private static Formula ProjectionFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), x = F.Id("X");
        Formula p = F.Id("P"), c = F.Id("c");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula matrix = Call("Matrix", n, n, complex);
        Formula positive = All("X", matrix, Seq(Call("PSD", x), Sp, Implies, Sp, Call("PSD", At(f, x))));
        Formula dominated = All("X", matrix, Seq(Call("PSD", x), Sp, Implies, Sp, At(f, x), Le, Sp, x));
        Formula projections = All("P", matrix, Seq(Adj(p), Eq, p, Sp, Land, Sp, p, p, Eq, p,
            Sp, Implies, Sp, At(f, p), Eq, c, p));
        Formula conclusion = Seq(Exists, Sp, c, InMacro, Sp, real, Comma, Sp,
            D(0), Le, Sp, c, Le, Sp, D(1), Sp, Land, Sp,
            At(f, F.Id("I")), Eq, c, F.Id("I"), Sp, Land, Sp, projections);
        return Disp(All("n", F.Id("Type"), Seq(
            Inst("Fintype", n), Inst("DecidableEq", n), Inst("Nonempty", n),
            All("f", Call("ComplexLinearMap", matrix, matrix),
                Seq(Grp(positive), Sp, Land, Sp, Grp(dominated), Sp, Implies, Sp, conclusion)))));
    }
}
