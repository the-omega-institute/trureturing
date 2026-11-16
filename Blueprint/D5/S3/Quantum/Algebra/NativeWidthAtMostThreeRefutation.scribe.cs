using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class NativeWidthAtMostThreeRefutationDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula SumOver(string name, Formula type, Formula term) =>
        Seq(new Formula.Subscript(Sum, Seq(V(name), Sp, Colon, Sp, type)), Sp,
            Parenthesized(term));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Mat(byte rows, byte cols) =>
        Call("Matrix", Call("Fin", D(rows)), Call("Fin", D(cols)), V("Complex"));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three independent native 3-by-5 and 5-by-3 coefficient matrices cannot produce a column isometry.",
        H("The native three-coefficient common-plane consumer"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-three-refutation"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/NativeWidthAtMostThreeRefutation.native_three_refutation"),
            H("No native column isometry from two independent triples"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let M range over all complex-linearly independent triples of 3-by-5 matrices, and N over all complex-linearly independent triples of 5-by-3 matrices. The Kronecker sum F has rows Fin 3 times Fin 5 and columns Fin 5 times Fin 3. The theorem says F*F cannot equal the identity on the latter carrier. There is no normalization, coefficient-kernel, plane, scalar cross-Gram, orthonormal embedding, or block-identity hypothesis.")),
                Paragraph(Text("NativeCoefficientWhitening.exact_whitening supplies an invertible coefficient change B, with M'=BM and N'=B inverse transpose N. It preserves the native Kronecker sum and independence of M, and derives sum_r M'(r)*M'(r)=I_5. Thus the coefficient-first stack S of M' is injective. CommonCoefficientPlane.common_plane then supplies one complex two-dimensional plane L neutral in the full sesquilinear pairing for every Hermitian T satisfying S*(T tensor I_3)S=0.")),
                Paragraph(Text("For each l,m in Fin 3, expansion of F*F gives the compression-kernel block T_lm(r,s)=(N'(r)*N'(s))_lm-delta_rs delta_lm. The compression is complex-linear and preserves conjugate transpose. Hence the Hermitian real and imaginary parts of each T_lm are both in the kernel; applying the same simultaneous plane to both parts proves full pairing neutrality for T_lm, including off-diagonal l,m.")),
                Paragraph(Text("Transport L by the explicit WithLp linear equivalence to EuclideanSpace, choose an orthonormal basis indexed by Fin 2, and write its columns as V. This constructs V*V=I_2. Define W_j,(r,l)=N'(r)_j,l and P=W*W on Fin 3 times Fin 3. With C=V tensor I_3, the neutral block equations give C*PC=I on Fin 2 times Fin 3. Rank multiplication bounds give rank(C*PC)<=rank(P)<=rank(W)<=5, whereas the identity on Fin 2 times Fin 3 has rank six, a contradiction.")),
                Paragraph(Text("This theorem addresses the exact independent-family k=3 case. The event definition also permits k=2 and is not refuted here. Reduction from unrestricted triples to a minimal independent decomposition, positive scalar normalization, and the original event with its eight dimension premises and both Gram implications are separate obligations. No classification, optimality, or resolution of that full event follows from this statement alone."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula M = V("M"), N = V("N");
        Formula r = V("r");
        Formula sum = SumOver("r", Call("Fin", D(3)),
            Call("kronecker", App(M, r), App(N, r)));
        Formula gram = new Formula.Binary(Call("conjTranspose", sum), FormulaBinaryOperator.Multiply, sum);
        Formula identity = Call("identity", Call("prod", Call("Fin", D(5)), Call("Fin", D(3))));
        Formula ne = new Formula.Relation(gram, FormulaRelationOperator.NotEqual, identity);
        return All("M", new Formula.TypeArrow(Call("Fin", D(3)), Mat(3, 5)),
            All("N", new Formula.TypeArrow(Call("Fin", D(3)), Mat(5, 3)),
                Imp(Call("LinearIndependent", V("Complex"), M),
                    Imp(Call("LinearIndependent", V("Complex"), N), ne))));
    }
}
