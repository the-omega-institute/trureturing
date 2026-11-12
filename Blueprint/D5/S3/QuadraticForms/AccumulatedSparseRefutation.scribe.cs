using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class AccumulatedSparseRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/QuadraticForms/AccumulatedSparseRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/ekene2026accumulatedpsd");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An equicorrelated positive semidefinite Euclidean contraction has accumulated best sparse squared errors exceeding one.",
        H("Accumulated sparse quadratic errors"),
        Blocks(
            Describe.Lean(DescribeId.Create("accumulated-sparse-quadratic"),
                DeclarationHandle.Create(Owner + "quadratic"), H("The quadratic form"),
                StatementSource.FromAuthor(Disp(All("y", Call("Euclidean", D(6,4)),
                    Equal(Call("Q", V("y")), Frac(Add(Call("A", V("y")), Pow(Call("B", V("y")), D(2))), D(1,2,8)))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real 64-coordinate vector y, let A(y) be the sum of its coordinate squares and B(y) the sum of its coordinates. For K=(I+J)/128, Q(y)=y-transpose K y=(A(y)+B(y)^2)/128. The Euclidean norm is used throughout."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-sparse-minimum"),
                DeclarationHandle.Create(Owner + "sparse_minimum"), H("The actual attained minimum"),
                StatementSource.FromAuthor(Disp(All("d", Call("Nat"),
                    Seq(D(1), Sp, Le, Sp, V("d"), Sp, Le, Sp, D(6,4), Sp, Rightarrow, Sp,
                        Call("IsLeast", Call("E", V("d")), Call("t", V("d"))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Here E(d) is the set of all values (x-z)-transpose K(x-z) with z real and at most d nonzero coordinates, x_i=1/8, and t(d)=65(64-d)/(8192(d+1)). There is no sign or magnitude restriction on z. Cauchy--Schwarz on the actual nonzero support gives the universal lower bound. On any d-element coordinate subset, z_i=65/(8(d+1)) and zero elsewhere attains it. Smaller supports, negative coefficients and cancellations are all included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-sparse-total"),
                DeclarationHandle.Create(Owner + "accumulation_gt_one"), H("Accumulation exceeds one"),
                StatementSource.FromAuthor(Disp(Seq(D(1), Sp, Lt, Sp, V("T")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("T is the sum of t(d) for d from 1 through 63, on the same fixed matrix and vector. Its strict inequality is an exact rational calculation. No errors from different matrices or incompatible vectors are combined."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("accumulated-sparse-refutation"),
                DeclarationHandle.Create(Owner + "result"), H("The full finite assertion is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, V("P")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("P denotes the original universal finite assertion: for every positive integer m, every real symmetric positive semidefinite Euclidean contraction K, and every nonnegative Euclidean unit vector x with K_ii at most x_i squared, the sum from d=1 to m-1 of the actual minimum over all real z of support cardinality at most d is at most one. The closed Lean definition claim quantifies over the full original domain. Its sum-of-coordinate-squares contraction condition is equivalent to the Euclidean operator contraction condition.")),
                    Paragraph(Text("The matrix K=(I+J)/128 and x_i=1/8 satisfy these hypotheses in dimension 64. The diagonal equals x_i squared. The quadratic identity proves positivity. Cauchy--Schwarz bounds the squared norm of Ky by (65/128)^2 times the squared norm of y, hence by the squared norm of y. The IsLeast theorem proves nonemptiness, a lower bound and attainment of every source error used in the sum. Thus the real infimum is an actual minimum, and T>1 contradicts P.")),
                    Paragraph(Text("Ekene E. posed both assertions in MathOverflow 509794 revision 2, licensed CC BY-SA 4.0. The finite and Hilbert negations are separate members of one source event. The shared component of the equicorrelated geometry leaves errors that accumulate across sparsity levels."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mathoverflow-509794-accumulated-sparse-errors"),
                    ResolutionKind.Refuted,
                    [DeclarationHandle.Create("D5/S3/HilbertOperators/Approximation/AccumulatedSupportRefutation.result")])))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args) =>
        args.Length == 0 ? V(s) : new Formula.Apply(V(s), [.. args]);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, V(s), Sp, Colon, Sp, type, Close, Comma, Sp, body);
}
