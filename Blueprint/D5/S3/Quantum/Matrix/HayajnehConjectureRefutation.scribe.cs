using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HayajnehConjectureRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/HayajnehConjectureRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/hayajneh2018uinorm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two positive definite rational matrices reverse the trace-norm comparison at powers "
        + "one half and three quarters, refuting the proposed monotonicity for all unitarily invariant norms.",
        H("A counterexample to mixed-power norm monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hayajneh-unitarily-invariant-conjecture"),
                DeclarationHandle.Create(Module + ".conjecture"),
                H("Conjecture 1 for every unitarily invariant norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let A be a positive semidefinite matrix and B be a Hermitian "
                        + "matrix. Then for 1/2 ≤ s ≤ t ≤ 1 and for every unitarily invariant norm, "
                        + "the proposed inequality is N(A^s B + B A^(1−s)) ≤ N(A^t B + B A^(1−t)).")),
                    Paragraph(Text("The formal proposition quantifies over every natural dimension n, "
                        + "all complex n by n matrices A and B, the positive semidefinite condition on A, "
                        + "the Hermitian condition on B, every real pair s,t in the displayed order, "
                        + "and every unitarily invariant norm on that matrix space. Matrix powers use "
                        + "continuous functional calculus on the positive semidefinite input. "
                        + "No additional lower spectral bound is imposed on A."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hayajneh-unitarily-invariant-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Conjecture 1 is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take n=2, A=diag(1/81,1), B=[[1,3/4],[3/4,1]], "
                        + "s=1/2 and t=3/4. Both matrices are positive definite, and B is Hermitian. "
                        + "Diagonal functional calculus gives A^(1/2)=diag(1/9,1), "
                        + "A^(1/4)=diag(1/3,1) and A^(3/4)=diag(1/27,1). "
                        + "Thus L=A^(1/2)B+BA^(1/2)=[[2/9,5/6],[5/6,2]] and "
                        + "R=A^(3/4)B+BA^(1/4)=[[10/27,7/9],[1,2]].")),
                    Paragraph(Text("The trace norm is an instance of the unitarily invariant norm "
                        + "interface. For every complex two by two matrix T, its square is "
                        + "tr(T* T)+2|det T|: the squared singular values sum to tr(T* T), "
                        + "and the product of the singular values is |det T|. This identity "
                        + "also applies to the non-Hermitian matrix R. Here det L=−1/4, "
                        + "det R=−1/27, the squared trace norm of L is 481/81, and that "
                        + "of R is 4240/729. Their difference is 89/729>0.")),
                    Paragraph(Text("Nonnegativity of both norms therefore gives N(L)>N(R) "
                        + "for the trace norm, contradicting the conjecture. The sum of both "
                        + "singular values is the full prefix in dimension two, so the same "
                        + "comparison obstructs weak majorization at that prefix. The known "
                        + "Hilbert–Schmidt case and the endpoint s=1/2,t=1 remain valid. "
                        + "This refutation does not decide the universal restrictions to "
                        + "Schatten exponents at least two or to the operator norm."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hayajneh-2018-unitarily-invariant-norm"),
                    ResolutionKind.Refuted)))));
}
