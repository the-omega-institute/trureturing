using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.OperatorMeans;

internal sealed class ConvexMixtureClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A convex family is closed under every binary convex mixture.",
        H("Convex Mixture Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("convex-mixture-mem"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/OperatorMeans/ConvexMixtureClosure.convex_mixture_mem"),
                H("Convex mixtures remain in a convex family"),
                StatementSource.FromAuthor(ConvexMixtureClosureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be a real module and let F be a convex family in E. If x and y "
                            + "belong to F and c lies in the closed unit interval, then the "
                            + "binary mixture c x + (1-c) y also belongs to F.")),
                    Paragraph(Text(
                        "This closes only the convex-mixture clause of pzg-v170 remark/27.702. "
                            + "It applies to a family of operator means once that family's "
                            + "convexity has been supplied; it does not establish Kubo--Ando "
                            + "convexity, identify the numerical root c-star, prove the monotonic "
                            + "mean chain, or claim transcendence.")),
                    Paragraph(Text(
                        "Repository searches found no equivalent D5 operator-mean declaration. "
                            + "Direct search of the pinned Mathlib source found that Convex itself "
                            + "supplies binary-combination closure. The Lean theorem is a thin "
                            + "wrapper converting membership in the unit interval into two "
                            + "nonnegative weights whose sum is one."))),
                DescribeRole.Theorem))));

    private static Formula ConvexMixtureClosureFormula()
    {
        Formula family = F.Id("F");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula coefficient = F.Id("c");

        return Disp(Seq(
            Operatorname, Grp(F.Id("Convex")), Underscore, Grp(Mathbb, Grp(F.Id("R"))),
            Open, family, Close, Sp, Land, Sp,
            first, Comma, Sp, second, Sp, InMacro, Sp, family, Sp, Land, Sp,
            coefficient, Sp, InMacro, Sp, OpenBracket, D(0), Comma, Sp, D(1), CloseBracket,
            Sp, Rightarrow, Sp,
            coefficient, Sp, Cdot, Sp, first, Sp, Plus, Sp,
            Open, D(1), Sp, Minus, Sp, coefficient, Close, Sp, Cdot, Sp, second,
            Sp, InMacro, Sp, family, Dot));
    }
}
