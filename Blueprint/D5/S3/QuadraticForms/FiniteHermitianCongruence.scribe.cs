using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class FiniteHermitianCongruenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hermitian matrix over a finite field with nontrivial involution has an identity block and a zero radical in one invertible basis.",
        H("Finite Hermitian Congruence"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-hermitian-congruence"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/FiniteHermitianCongruence.finite_hermitian_congruence"),
            H("Normalized orthogonal basis including the radical"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/QuadraticForms/fulton1977hermitian")),
            Blocks(
                Paragraph(Text("Let K be any finite field, sigma a ring automorphism of K with sigma(sigma(x))=x for every x and sigma different from the identity, N any natural number, and B an N by N matrix satisfying transpose(map(sigma,B))=B. There is an invertible N by N matrix T with transpose(T) B map(sigma,T) equal to the diagonal matrix whose i-th entry is one when i.val is less than rank(B), and zero otherwise. All matrix entries lie in K. The involution acts entrywise on both B and the same T.")),
                Paragraph(Text("The associated form b(x,y)=x-transpose B sigma(y) is linear in its first argument and sigma-semilinear in its second. It satisfies sigma(b(x,y))=b(y,x). If every b(x,x) were zero, comparing the self-pairings of x+y and x+c y for a scalar c with sigma(c) different from c would force every b(x,y) to vanish. Thus every nonzero form has a nonzero self-pairing.")),
                Paragraph(Text("The pivot value a=b(x,x) lies in the fixed field of sigma. Surjectivity of the finite-field norm and its formula c sigma(c) choose c with c sigma(c)=a-inverse. The vector e=c x then has b(e,e)=1. The kernel of the linear functional y mapped to b(y,e) is complementary to the line K e and orthogonal to e in both arguments. Its dimension is one less, so dimension induction constructs a complete normalized orthogonal basis.")),
                Paragraph(Text("When the restricted form is zero, any basis supplies the remaining radical vectors. The induction starts at dimension zero with the empty basis. Invertibility of the basis matrix T and of its sigma image preserves matrix rank, so the number of unit diagonal entries is exactly rank(B). Singular forms, the zero matrix, and N=0 are included; no orthogonal basis or norm-surjectivity premise is supplied.")),
                Paragraph(Text("This is established finite-field Hermitian-form mathematics. Fulton gives the arbitrary-rank characteristic-two congruence on page 170 of the cited paper. The characteristic-two case is included in the displayed theorem. Its conclusion concerns the matrix congruence; character sums and rank-parity or entropy formulas require additional results."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var k = F.Id("K");
        var sigma = F.Id("sigma");
        var n = F.Id("N");
        var b = F.Id("B");
        var t = F.Id("T");
        var i = F.Id("i");
        var matrix = Call("Matrix", Call("Fin", n), Call("Fin", n), k);
        var hypotheses = Seq(Call("Involutive", sigma), Sp, Land, Sp,
            sigma, Sp, Neq, Sp, Call("RingEquivRefl", k), Sp, Land, Sp,
            Call("transpose", Call("map", b, sigma)), Sp, Eq, Sp, b);
        var diagonal = Call("diagonal", Seq(Typed(i, Call("Fin", n)), Sp, Mapsto, Sp,
            Call("ite", Seq(Call("val", i), Sp, Lt, Sp, Call("rank", b)), D(1), D(0))));
        var conclusion = Some(t, matrix, Seq(Call("IsUnit", t), Sp, Land, Sp,
            Call("transpose", t), Sp, Cdot, Sp, b, Sp, Cdot, Sp, Call("map", t, sigma),
            Sp, Eq, Sp, diagonal));
        return All(k, Call("Type"), Seq(OpenBracket, Call("Field", k), CloseBracket, Sp,
            OpenBracket, Call("Finite", k), CloseBracket, Sp,
            All(sigma, Call("RingEquiv", k, k), All(n, Seq(Mathbb, Grp(F.Id("N"))),
                All(b, matrix, Seq(Open, hypotheses, Close, Sp, Rightarrow, Sp, conclusion))))));
    }

    private static Formula Typed(Formula name, Formula type) => Seq(Open, name, Sp, Colon, Sp, type, Close);
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp, Typed(name, type), Comma, Sp, body);
    private static Formula Some(Formula name, Formula type, Formula body) => Seq(Exists, Sp, Typed(name, type), Comma, Sp, body);
}
