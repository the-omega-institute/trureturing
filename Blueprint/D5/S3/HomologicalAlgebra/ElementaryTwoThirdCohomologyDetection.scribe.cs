using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class ElementaryTwoThirdCohomologyDetectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All cyclic restrictions detect third cohomology of elementary two-groups with divisible-by-two coefficients.",
        H("Cyclic Detection of Actual Third Cohomology"),
        Blocks(Describe.Lean(
            DescribeId.Create("elementary-two-third-cohomology-detection"),
            DeclarationHandle.Create("D5/S3/HomologicalAlgebra/ElementaryTwoThirdCohomologyDetection.cyclic_restriction_detects_third_cohomology"),
            H("All finite ranks and all nonidentity cyclic subgroups"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let M be an additive commutative group with surjective doubling. "
                    + "For a natural number r, write E(r) = Multiplicative(Fin r to ZMod 2). "
                    + "Here H3(E(r),M) means Mathlib groupCohomology of Rep.trivial Z E(r) M "
                    + "in degree three. Res(g) is its inclusion-induced map to the cohomology "
                    + "of Subgroup.zpowers g, with the restricted trivial representation. "
                    + "Every actual class whose restrictions vanish for every nonidentity g is zero. "
                    + "The empty rank and rank one are included.")),
                Paragraph(Text("The proof chooses an actual cocycle representative and constructs "
                    + "one global two-cochain. On arbitrary unnormalized input, the cyclic invariant "
                    + "is f(g,g,g) + f(g,1,g). The normalizing correction is retained through a "
                    + "four-term product comparison. Its two mixed functions are extracted from "
                    + "the same cocycle and satisfy the joint equations du = 0 and 2u + dv = 0. "
                    + "Halving v corrects u to a two-torsion cocycle with zero diagonal. "
                    + "A projective section supplies its primitive, and rank induction combines "
                    + "all corrections into one boundary of the original cocycle.")),
                Paragraph(Text("Additive Circle has surjective doubling through the actual Circle "
                    + "exponential, so these coefficients give U(1) with trivial action. "
                    + "Checking only coordinate generators is not the premise. The result "
                    + "does not assert an integral homology decomposition, a classification or "
                    + "count of representative families, a vertex-algebra realization, or a "
                    + "discrete-torsion interface. No originality claim is made."))),
            DescribeRole.Theorem))));

    private static Formula Statement() => Disp(Seq(
        Forall, Sp, Open, F.Id("M"), Colon, Sp, F.Id("Type"), Close, Sp,
        OpenBracket, F.Id("AddCommGroup"), Sp, F.Id("M"), CloseBracket, Comma, Sp,
        Open, Forall, Sp, F.Id("m"), Colon, Sp, F.Id("M"), Comma, Sp,
        Exists, Sp, F.Id("k"), Colon, Sp, F.Id("M"), Comma, Sp,
        F.Id("k"), Plus, F.Id("k"), Eq, F.Id("m"), Close, Sp, Rightarrow, Sp,
        Forall, Sp, Open, F.Id("r"), Colon, Sp, Mathbb, Grp(F.Id("N")), Close, Sp,
        Open, F.Id("c"), Colon, Sp, F.Id("H3"), Open, F.Id("E"), Open, F.Id("r"), Close,
        Comma, F.Id("M"), Close, Close, Comma, Sp,
        Open, Forall, Sp, F.Id("g"), Colon, Sp, F.Id("E"), Open, F.Id("r"), Close, Comma, Sp,
        F.Id("g"), Neq, D(1), Sp, Rightarrow, Sp,
        F.Id("Res"), Open, F.Id("g"), Close, Open, F.Id("c"), Close, Eq, D(0), Close,
        Sp, Rightarrow, Sp, F.Id("c"), Eq, D(0)));
}
