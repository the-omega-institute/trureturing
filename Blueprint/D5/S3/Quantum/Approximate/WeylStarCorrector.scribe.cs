using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Approximate;

internal sealed class WeylStarCorrectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete normalized Weyl family supplies a contractive diagonal for every positive matrix size and hence the same exact-correction constants.",
        H("Full-matrix Weyl star correction"), Blocks(
            Paragraph(Text("Fix a natural n with n nonzero. Weyl coordinates are ZMod n, with all n^2 ordered labels. The final source coordinates are Fin n, obtained by the canonical finite reindexing. The source is the full matrix algebra on those coordinates; its norm is the Euclidean L2 operator norm and its star is conjugate transpose. This includes n=1 and every composite size. The target is any complex C-star algebra, independently of n.")),
            Paragraph(Text("The actual word U(a,b) is shiftMatrix(n)^a.val times clockMatrix(n)^b.val. The left leg is (n^2)^(-1) star(U(a,b)); the right leg is U(a,b). In particular the adjoint retains the Weyl phase. Each word is unitary, both word and adjoint have operator norm one, and the weighted sum of norm products is exactly one.")),
            Paragraph(Text("Character orthogonality evaluates the weighted tensor coefficient at (i,j,k,l) to n^(-1) when l=i and k=j, and to zero otherwise. Thus the tensor is n^(-1) sum E(i,j) tensor E(j,i). Matrix-unit multiplication proves centrality for every full source matrix. A complex star-algebra equivalence transports the packet to Fin n and preserves the operator norm. The product of the legs sums to the identity. The diagonal defined here supplies all three properties to the correction theorem.")),
            Describe.Lean(DescribeId.Create("full-matrix-weyl-exact-star-correction"),
                DeclarationHandle.Create("D5/S3/Quantum/Approximate/WeylStarCorrector.exists_matrix_star_hom_close"),
                H("Uniform correction in the actual full matrix algebra"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Apply the finite-diagonal correction to this exact Weyl packet. PreservesStar is exact star preservation, while DefectBound f d quantifies norm(f(XY)-f(X)f(Y))<=d norm(X) norm(Y) over every pair of source matrices. The initial unit error is at most one quarter, and 0<=d<=1/32. The output is a genuine unital complex star-algebra homomorphism with the stated distance from this same f.")),
                    Paragraph(Text("The tensor, unitary and normalization identities supply a dimension-free norm budget. No unweighted n^2 error sum is introduced. The construction requires no CP or UCP data, no column compatibility, no supplied representation and no equality between source and target dimensions. For a Hilbert-operator target the complex inner-product structure and completeness must belong to the actual target space. No algebra structure on an unrelated nonassociative product is asserted.")),
                    Paragraph(Text("The finite averaging formula is associated with arXiv:2405.02434v2. The conclusion is the matrix application of the finite-diagonal theorem; deriving a particular compressed action and its quantitative input estimates is a separate mathematical obligation."))),
                DescribeRole.Theorem))));

    private static Formula X(string n) => F.Id(n);
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Inst(Formula x, Formula body) => F.Seq(F.OpenBracket,x,F.CloseBracket,F.Sp,body);
    private static Formula Statement()
    {
        Formula n=X("n"), a=X("A"), f=X("f"), d=X("d"), x=X("X");
        Formula z=Call("Fin",n), mat=Call("Matrix",z,z,Call("Complex"));
        Formula close=All("X",mat,Le(new Formula.Norm(Subtract(At(X("rho"),x),At(f,x))),
            Multiply(new Formula.Fraction(Multiply(Num(8),d),Num(3)),new Formula.Norm(x))));
        Formula result=Ex("rho",Call("ComplexStarAlgHom",mat,a),close);
        Formula hypotheses=And(Le(Num(0),d),And(Le(d,new Formula.Fraction(Num(1),Num(32))),
            And(Call("PreservesStar",f),And(Call("DefectBound",f,d),
                Le(new Formula.Norm(Subtract(At(f,Num(1)),Num(1))),new Formula.Fraction(Num(1),Num(4)))))));
        Formula statement=All("f",Call("ComplexCLM",mat,a),All("d",Call("Real"),Imp(hypotheses,result)));
        statement=All("A",Call("Type"),Inst(Call("CStarAlgebra",a),statement));
        return All("n",Call("Nat"),Inst(Call("NeZero",n),statement));
    }
}
