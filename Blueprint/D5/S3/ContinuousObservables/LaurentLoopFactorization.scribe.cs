using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class LaurentLoopFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Special-unitary Laurent loops of actual degree n have a unique ordered factorization into exactly n primitive projector factors and a constant.",
        H("Exact ordered factorization of Laurent loops"),
        Blocks(
            Paragraph(Text("Write M for the two-by-two complex matrices and L for matrices of scalar complex Laurent polynomials. A finitely supported family C:Z -> M is represented entrywise by F=ofCoefficients(C); its coefficient at every integer j is exactly C(j). For a nonzero complex unit z, evaluate(F,z) evaluates each scalar Laurent entry. CircleSU(F) means evaluate(F,z)* evaluate(F,z)=I and det(evaluate(F,z))=1 for every z of norm one, where the first star denotes conjugate transpose.")),
            Paragraph(Text("InClass(n,F) requires CircleSU(F) and C(j)=0 whenever |j|>n or j is not congruent to n modulo two. ActualDegree(n,F) requires C(n) != 0 or C(-n) != 0. RankOneProjector(P) means P*=P, P P=P and complex rank(P)=1. The primitive factor is E(P)=tP+t^(-1)(I-P). All these conditions refer to the full unit circle and to arbitrary matrix coefficients.")),
            Describe.Lean(
                DescribeId.Create("haah-exact-ordered-laurent-loop-factorization"),
                DeclarationHandle.Create("D5/S3/ContinuousObservables/LaurentLoopFactorization.haah_factorization"),
                H("Forward class membership and unique exact-length decomposition"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/ContinuousObservables/haah2019productdecomposition")),
                Blocks(
                    Paragraph(Text("In the display, projectors(Ps) means every member of the ordered list Ps is a rank-one orthogonal projector. The first clause quantifies over every such finite list and asserts class membership of its product, with n equal to its length. The second clause quantifies over every natural n and every finitely supported C satisfying the stated support, parity, actual-degree and circle conditions. Factorization(n,F,(A,Ps)) means A* A=I, det(A)=1, length(Ps)=n, projectors(Ps), and F=constant(A) times the product of E(P) in list order. Thus the unique witness contains both the arbitrary SU(2) constant and the whole ordered list. Equality holds in L, hence at every Laurent coefficient.")),
                    Paragraph(Text("The full-circle hypothesis first yields Laurent identities F* F=I, F F*=I and det(F)=1, with the formal adjoint combining coefficient conjugation, transpose and exponent inversion. Clearing negative powers and the infinite-root theorem for complex polynomials justify passage from circle values to identities. The extreme coefficients imply that both endpoint matrices are singular and their row spaces satisfy the required orthogonality relations.")),
                    Paragraph(Text("For a nonzero singular endpoint A, the normalized Gram matrix P=(A* A)/Tr(A* A) is self-adjoint, idempotent and has rank one, and A P=A. A rank-one orthogonal projection with this property is unique. For a nonzero positive endpoint this gives the unique terminal projection; if that endpoint is zero, the nonzero negative endpoint supplies the complement. The two cancellation equations are C(n)(I-P)=0 and C(-n)P=0.")),
                    Paragraph(Text("For n=m+1, the residual G=F E(I-P) belongs to InClass(m) and F=G E(P). The residual has actual degree m: otherwise the reconstruction would make both original endpoints vanish. The named construction decompose recursively applies this step and appends P on the right. At zero degree F is its constant coefficient, which is an arbitrary SU(2) matrix, and the list is empty. Any other exact-length factorization has the same last projection by the endpoint cancellation equations; canceling it reduces ordered uniqueness to the same residual at the preceding degree.")),
                    Paragraph(Text("The forward product need not have actual degree equal to its list length. Uniqueness applies to the actual-degree input with exactly n factors; it asserts neither angle uniqueness nor uniqueness of padded lists. No inversion or equatorial symmetry, scalar completion, numerical stability, efficient synthesis, singular-value or query bound, or physical implementation is included. The statement is Haah's algebraic factorization theorem, Definition 1 and Theorem 2 on printed pages 4–5, using the primitive convention of equation (2) on page 3."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula p) => Seq(Open, p, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
    private static Formula All(string s, Formula domain, Formula p) =>
        Seq(Forall, Sp, Par(Seq(V(s), Colon, Sp, domain)), Comma, Sp, p);
    private static Formula And(Formula p, Formula q) => Seq(Par(p), Sp, Land, Sp, Par(q));
    private static Formula Statement()
    {
        var forward = All("Ps", Call("List", V("M")), Seq(
            Call("projectors", V("Ps")), Sp, Rightarrow, Sp,
            Call("InClass", Call("length", V("Ps")), Call("prod", Call("map", V("E"), V("Ps"))))));
        var hypotheses = And(Call("InClass", V("n"), Call("ofCoefficients", V("C"))),
            Call("ActualDegree", V("n"), Call("ofCoefficients", V("C"))));
        var converse = All("n", Seq(Mathbb, Grp(V("N"))), All("C", Call("Finsupp", V("Z"), V("M")),
            Seq(hypotheses, Sp, Rightarrow, Sp, Exists, Bang, Sp,
                Par(Seq(V("r"), Colon, Sp, V("M"), Times, Call("List", V("M")))), Comma, Sp,
                Call("Factorization", V("n"), Call("ofCoefficients", V("C")), V("r")))));
        return And(forward, converse);
    }
}
