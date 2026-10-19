using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class UniformRankFourNecessaryDocument : IScribeDocumentDefinition
{
    private static Formula X(string n) => F.Id(n);
    private static Formula D(long n) => Num(n);
    private static Formula R => Seq(Mathbb, Grp(X("R")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(X(n), [.. xs]);
    private static Formula All(string n, Formula t, Formula f) => Seq(Forall, Sp, Par(Seq(X(n), Colon, t)), Comma, Sp, f);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula Product(Formula a, Formula b) => Par(Seq(a, Times, Sp, b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Rightarrow, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Land, Sp, Par(b));
    private static Formula Fin(Formula n) => Call("Fin",n);
    private static Formula N => Seq(X("m"), Cdot, Sp, X("n"));
    private static Formula J => Product(Fin(X("m")),Fin(X("n")));
    private static Formula LabelledDiagonal()
    {
        var entry=Call("ofReal",Call("l",Call("e",X("p"))));
        return Call("diagonal",Par(Seq(X("fun"),Par(Seq(X("p"),Colon,J)),Mapsto,Sp,entry)));
    }
    private static Formula Statement() =>
        All("m",X("Nat"),All("n",X("Nat"),Imp(And(Le(D(4),X("m")),Le(D(4),X("n"))),
            All("e",Call("Equiv",J,Fin(N)),All("l",Arrow(Fin(N),R),
                Imp(Call("APPT",LabelledDiagonal()),Le(Call("sumFirst",D(6),X("l")),Call("sumLast",D(10),X("l")))))))));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual four-by-four product corner imposes a six-versus-ten mass inequality on every labelled APPT diagonal.",
        H("Uniform rank-four necessary inequality"), Blocks(
            Describe.Lean(DescribeId.Create("uniform-rank-four-necessary"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/UniformRankFourNecessary.uniform_rank_four_necessary"),
                H("First six versus last ten"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/hildebrand2007pptspectra")),
                Blocks(
                    Paragraph(Text("For arbitrary natural m,n at least four, an arbitrary equivalence e:(Fin m × Fin n) ≃ Fin(mn), and arbitrary real l:Fin(mn)→R, assume the actual complex diagonal diag(l composed with e) is APPT: its second-factor partial transpose is positive semidefinite after every global unitary on the full product. Then the sum of coordinates 0 through 5 is at most the sum of coordinates mn−10 through mn−1. The sumFirst and sumLast definitions use zero for out-of-range coordinates; the dimension hypotheses put all sixteen chosen coordinates in range. No ordering, nonnegativity, total mass, strict positivity or distinctness of l is required. Without ordering these are labelled coordinate sums, rather than a claim about largest and smallest eigenvalues.")),
                    Paragraph(Text("Inside Fin 4 × Fin 4 let eta=sum_a |aa>. The partial transpose of |eta><eta| is the swap. Its six antisymmetric columns have eigenvalue −1, while its six symmetric off-diagonal and four diagonal columns have eigenvalue +1. The explicit pair rotation assigns the first six values to the former columns and the last ten to the latter. An injective corner and a finite-complement permutation extend this assignment to the whole product. APPT positivity tested at eta and partial_transpose_trace_duality give last10−first6≥0. Only product compression is commuted with partial transpose; an arbitrary labelling is used through global unitary conjugation, with no covariance assertion about that labelling. This is a fixed rank-four instance of the Hildebrand spectral-testing framework, not a generic-rank criterion or a sufficient condition for APPT. The published framework and the prior availability of private construction steps are not claimed as new discoveries."))),
                DescribeRole.Theorem))));
}
