using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class RelativeQuotientDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closed inclusion splits its ambient subspace and identifies the relative quotient.",
        H("Relative Quotient Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relative-quotient-orthogonal-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Completion/RelativeQuotientDecomposition."
                        + "relative_quotient_orthogonal_decomposition"),
                H("A relative quotient is the orthogonal residual"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let M and N be closed subspaces of a complete real-or-complex "
                            + "inner-product space, with M contained in N. The copy of M inside "
                            + "N is constructed as the range of the induced isometric inclusion, "
                            + "and its orthogonal complement is therefore relative to N.")),
                    Paragraph(Text(
                        "The first conjunct states that these two subspaces are complementary. "
                            + "The remaining conjuncts name the canonical quotient map and state "
                            + "that it is both an isometry and a bijection from N modulo M onto "
                            + "the relative orthogonal complement.")),
                    Paragraph(Text(
                        "Repository search found and directly applies "
                            + "quotient_orthogonal_complement_isometry. Pinned Mathlib search "
                            + "found and reuses Submodule.isCompl_orthogonal and "
                            + "Submodule.quotientEquivOrthogonal. No exact theorem was found that "
                            + "packages both clauses for two named closed subspaces."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula DecompositionFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("E");
        Formula small = F.Id("M");
        Formula large = F.Id("N");
        Formula included = Call("include", small, large);
        Formula residual = Seq(included, Caret, Grp(Perp));
        Formula quotientMap = Call("relativeQuotientIsometry", small, large);

        return Disp(Seq(
            Forall, Sp, scalar, Colon, Sp,
            Operatorname, Grp(F.Id("RCLike")), Comma, Esc,
            Forall, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("CompleteInnerProductSpace")), Underscore,
            Grp(scalar), Comma, Esc,
            Forall, Sp, small, Comma, Sp, large, Colon, Sp,
            Call("ClosedSubmodule", scalar, space), Comma, Esc,
            small, Sp, Subseteq, Sp, large, Sp, Rightarrow, Sp,
            Call("IsCompl", included, residual), Sp, Land, Esc,
            Call("Isometry", quotientMap), Sp, Land, Sp,
            Call("Bijective", quotientMap), Dot));
    }
}
