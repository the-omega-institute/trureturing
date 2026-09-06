using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.PochhammerDeformation;

internal sealed class QuadraticRadiiDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/PochhammerDeformation/QuadraticRadii.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Zeros/vishnyakova2026polynomially");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive a, the quadratic Pochhammer class has outer radius a+1 "
            + "and inner radius (a+sqrt(a(a+1)))/2, both attained.",
        H("Exact Quadratic Root Radii"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quadratic-admissible-class"),
                DeclarationHandle.Create(Prefix + "U2"),
                H("The full degree-two class"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "U2 consists of all real polynomials of degree two whose image under "
                        + "the frozen Pochhammer operator has every complex root real and "
                        + "in [-1,0]. The original polynomial need not be monic or real-rooted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("complex-root-norms"),
                DeclarationHandle.Create(Prefix + "rootNorms"),
                H("Norms of complex zeros"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A root norm is the norm of a complex number at which the real polynomial "
                        + "evaluates to zero. The definition uses algebra evaluation into C."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-outer-extremum"),
                DeclarationHandle.Create(Prefix + "R2"),
                H("Outer radius"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "R2 is the supremum, over U2, of the supremum of each polynomial's "
                        + "root norms. For degree two the nonempty finite root set makes the "
                        + "inner supremum the largest root norm, as in Open Problem 7.2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-inner-extremum"),
                DeclarationHandle.Create(Prefix + "r2"),
                H("Inner radius"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "r2 is the supremum, over U2, of the infimum of each polynomial's "
                        + "root norms, corresponding to the smallest root norm in Open Problem 7.1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("monic-inverse-image"),
                DeclarationHandle.Create(Prefix + "normalQuadratic"),
                H("The normalized inverse image"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The polynomial is x^2+((a+1)(u+v)-1)x+a(a+1)uv. Its transformed "
                        + "image is a(a+1)(z+u)(z+v)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("full-quadratic-normal-form"),
                DeclarationHandle.Create(Prefix + "quadratic_normal_form"),
                H("Equivalence with the parameter square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Membership in U2 is equivalent to being a nonzero real scalar multiple "
                        + "of a normalQuadratic with u,v in [0,1]. The proof reuses the frozen "
                        + "operator and Mathlib's factorization over the complex numbers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-outer-estimate"),
                DeclarationHandle.Create(Prefix + "normal_outer_bound"),
                H("Every root lies in the outer disk"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Every complex zero of every normalQuadratic from the parameter square "
                        + "has norm at most a+1. Real roots are controlled by coefficient and "
                        + "endpoint inequalities; nonreal roots have squared norm a(a+1)uv."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-inner-estimate"),
                DeclarationHandle.Create(Prefix + "normal_inner_bound"),
                H("Some root lies in the sharp inner disk"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Put M=(a+sqrt(a(a+1)))/2 and q=sqrt(a(a+1)uv). If q<=M, the "
                        + "root product gives a root of norm at most M. Otherwise AM-GM gives "
                        + "p(-M)<=(q-M)(q-M-1)<0, and the intermediate value theorem supplies "
                        + "a real zero in [-M,0]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("outer-radius-witness"),
                DeclarationHandle.Create(Prefix + "quadratic_outer_witness"),
                H("The corner witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At u=v=1 the admissible polynomial factors as (x+a)(x+a+1), "
                        + "and the zero -(a+1) attains the outer bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("inner-radius-witness"),
                DeclarationHandle.Create(Prefix + "quadratic_inner_witness"),
                H("The repeated-root witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Writing s=sqrt(a(a+1)) and M=(a+s)/2, the parameter u=v=M/s "
                        + "belongs to the unit square and yields (x+M)^2. The identity "
                        + "M=a+c2(a) and its admissibility reuse the frozen interval theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("open-problem-seven-two-quadratic"),
                DeclarationHandle.Create(Prefix + "quadratic_outer_radius"),
                H("Open Problem 7.2 in degree two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every a>0, R2(a)=a+1. This proves the degree-two case of the "
                        + "paper's conjectured formula R_n=a+n-1; no assertion about n>2 is made."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("open-problem-seven-one-quadratic"),
                DeclarationHandle.Create(Prefix + "quadratic_inner_radius"),
                H("Open Problem 7.1 in degree two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every a>0, r2(a)=(a+sqrt(a(a+1)))/2. The paper states this "
                        + "expression as a lower bound; the uniform inner estimate proves "
                        + "equality. This result does not assert a bound uniform in the degree."))),
                DescribeRole.Theorem))));
}
