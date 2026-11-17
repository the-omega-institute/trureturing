using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeRectangularBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An arbitrary native sum of three rectangular tensor products with positive scalar column Gram and 3a < 2b satisfies 2c <= d.",
        H("The native rectangular width-three dimension bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("native-rectangular-bound"),
            DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeRectangularBound.bound"),
            H("Arbitrary tensor factors and positive scalar column Gram"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let a,b,c,d be arbitrary natural dimensions, M(r) complex a-by-b matrices and " +
                    "N(r) complex d-by-c matrices, indexed by r in Fin 3. The matrix F is the sum " +
                    "of M(r) tensor N(r), with rows (i,j) in Fin a times Fin d and columns (l,m) " +
                    "in Fin b times Fin c. If lambda is real and positive, F*F=lambda I, and " +
                    "3a < 2b, then 2c <= d. There is no factor-independence assumption. Every zero " +
                    "dimension is included, with the c=0 case immediate.")),
                Paragraph(Text(
                    "When 2a<b, the stronger existing native scalar-Gram obstruction gives 3c<=d. " +
                    "In the remaining range, choose an exact tensor decomposition of minimal width " +
                    "k at most three. A linear dependence on either side would remove a term, so " +
                    "both factor families are independent. Scaling one family by the reciprocal " +
                    "square root of lambda gives an identity column Gram without changing k.")),
                Paragraph(Text(
                    "For c>0, the normalized Hilbert-Schmidt Gram H(r,s)=trace(N(r)^* N(s))/c " +
                    "is positive definite. Factor H=B*B and mix the M family by B, the N family " +
                    "by the inverse transpose of B. This preserves the native tensor sum. Taking " +
                    "a partial trace of its column Gram shows that the new M stack is an isometry. " +
                    "Widths zero and one contradict the dimension bound for this injective stack. " +
                    "At width two, the strict inequality 2b>3a and the product-rank inequalities " +
                    "make the entire coefficient-compression map injective. Every opposite Gram " +
                    "block is then the identity coefficient block, so concatenation has 2c " +
                    "orthonormal columns in dimension d.")),
                Paragraph(Text(
                    "At width three, the generic common-plane theorem gives a single neutral " +
                    "complex coefficient plane L for the whole Hermitian compression kernel. " +
                    "For each opposite complex Gram block, subtract its identity block and split " +
                    "the result into Hermitian real and imaginary parts. Both compress to zero " +
                    "and use this same L. Their complex recombination therefore vanishes on L " +
                    "as a full sesquilinear pairing. Choosing an orthonormal basis V of L and " +
                    "restricting the concatenated N Gram by V tensor I_c produces an identity " +
                    "Gram on Fin 2 times Fin c. Its rank is 2c and cannot exceed d. This proof " +
                    "uses the tensor Gram blocks throughout; the ambient inequality bc<=ad " +
                    "alone does not yield the conclusion."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Fin(string n) => Call("Fin", V(n));
    private static Formula Matrices(string rows, string cols) =>
        new Formula.TypeArrow(Call("Fin", D(3)),
            Call("Matrix", Fin(rows), Fin(cols), V("Complex")));

    private static Formula Statement()
    {
        Formula a = V("a"), b = V("b"), c = V("c"), d = V("d"), lambda = V("lambda");
        Formula r = V("r");
        Formula Fsum = Seq(new Formula.Subscript(Sum,
                Seq(r, Colon, Call("Fin", D(3)))), Sp,
            Call("kronecker", Apply(V("M"), r), Apply(V("N"), r)));
        Formula gram = Equal(Mul(Call("conjTranspose", Fsum), Fsum),
            Call("smul", Call("ofReal", lambda), Seq(Open, D(1), Colon,
                Call("Matrix", Call("Prod", Fin("b"), Fin("c")),
                    Call("Prod", Fin("b"), Fin("c")), V("Complex")), Close)));
        Formula body = All("M", Matrices("a", "b"), All("N", Matrices("d", "c"),
            All("lambda", V("Real"), Imp(Less(D(0), lambda),
                Imp(Less(Mul(D(3), a), Mul(D(2), b)), Imp(gram, Le(Mul(D(2), c), d)))))));
        return All("a", V("Nat"), All("b", V("Nat"), All("c", V("Nat"), All("d", V("Nat"), body))));
    }
}
