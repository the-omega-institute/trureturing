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
                    Paragraph(Text("This projection conclusion is an intermediate consequence for positive refinements of a canonical filter. The matrix-span and positive compression results below extend this conclusion and identify input kernel directions and original direct-sum centers. The complete singular scalar formula and the complete positivity of all original records require their full support-corner application. No assertion about an unrelated coarse completely positive map follows from this projection statement."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("matrix-projection-span"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/PositiveRefinementRigidity.eq_of_projection_eq"),
                H("Projections determine a complex linear matrix map"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For any finite decidable coordinate type n and any complex module V with an additive commutative group, two complex linear maps from M_n(C) to V are equal if they agree on every Hermitian idempotent. Unitary diagonalization expresses every Hermitian matrix as a linear combination of orthogonal projections. Real and imaginary self-adjoint parts then give every complex matrix. Empty coordinate types are included."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("identity-dominated-scalar"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/PositiveRefinementRigidity.identity_dominated_scalar"),
                H("Scalar action on every complex matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For any finite decidable coordinate type n with a chosen coordinate, let Phi be a complex linear matrix endomorphism. If Phi maps every PSD input to a PSD matrix and Phi(X) is at most X on every PSD input, there exists a real c with zero at most c at most one such that Phi(X)=c X for every complex matrix X. Positivity is the only map-positivity premise."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-projection-compression"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/PositiveRefinementRigidity.positive_map_projection_compression"),
                H("A vanished projection removes its cross terms"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For arbitrary finite decidable input and output coordinate types n and m, let Phi:M_n(C) to M_m(C) be complex linear and positive on every PSD input. For every Hermitian idempotent P, if Phi(I-P)=0, then Phi(P X P)=Phi(X) for every complex matrix X. Positive output trace functionals and Cauchy-Schwarz remove both cross terms. Complete positivity is not assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-refinement-structure"),
                DeclarationHandle.Create("D5/S3/Quantum/Reduction/PositiveRefinementRigidity.canonical_refinement_structure"),
                H("Original labels preserve the unequal direct-sum centers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Let A be any finite set of original fine records, B any finite decidable set of centers, and d(b) arbitrary finite decidable coordinate types, without an equal-dimension assumption. Let R(b) be square complex matrices and S(a) complex linear endomorphisms of the product of the matrix blocks. Assume each S(a) maps every componentwise PSD input to a componentwise PSD output and, for every input X and center b, the sum over the same labels a of S(a)(X)(b) equals R(b) X(b) R(b)*. Then S(a)(X)(b) equals S(a) applied to the input with only block b retained, evaluated at b. If R(b)=0, that output vanishes for every X. For every Hermitian idempotent P in block b with R(b) P=R(b), replacing the single input block X by P X P leaves that output unchanged. Zero blocks and empty finite carriers are included. No fine record is replaced by a Kraus index."))),
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
