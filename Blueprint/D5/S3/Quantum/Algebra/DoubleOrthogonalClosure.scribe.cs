using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class DoubleOrthogonalClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Double orthogonal complementation equals topological closure in a Hilbert space.",
        H("Double Orthogonal Complement and Closure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("double-orthogonal-complement-equals-closure"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/DoubleOrthogonalClosure."
                    + "double_orthogonal_complement_eq_closure"),
                H("Double orthogonal complement equals closure"),
                StatementSource.FromAuthor(DoubleOrthogonalClosureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k be a real-or-complex scalar field, E a complete inner-product "
                            + "space over k, and M an arbitrary linear subspace. Taking the "
                            + "orthogonal complement twice produces exactly the topological "
                            + "closure of M.")),
                    Paragraph(Text(
                        "This closes the primary boxed equality in qdo-v1 theorem/28.6. The "
                            + "closed-subspace and finite-dimensional special cases follow by "
                            + "identifying the topological closure with M; they are not claimed as "
                            + "separate declarations here.")),
                    Paragraph(Text(
                        "Repository search found no equivalent D5 declaration. Loogle and direct "
                            + "search of the pinned Mathlib source found the exact theorem "
                            + "Submodule.orthogonal_orthogonal_eq_closure, which the Lean module "
                            + "imports and applies directly. The local smart-search name query did "
                            + "not find that declaration."))),
                DescribeRole.Theorem))));

    private static Formula DoubleOrthogonalClosureFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("E");
        Formula subspace = F.Id("M");
        Formula Orthogonal(Formula value) => Call("orthogonal", value);

        return Disp(Seq(
            Forall, Sp, scalar, Comma, Sp, space, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("RCLike")), Open, scalar, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("NormedAddCommGroup")), Open, space, Close,
            CloseBracket, Comma, Esc,
            OpenBracket,
            Operatorname, Grp(F.Id("InnerProductSpace")), Underscore, Grp(scalar),
            Open, space, Close, CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("CompleteSpace")), Open, space, Close,
            CloseBracket, Comma, Esc,
            subspace, Colon, Sp, Operatorname, Grp(F.Id("Submodule")), Underscore,
            Grp(scalar), Open, space, Close, Comma, Esc,
            Orthogonal(Orthogonal(subspace)), Sp, Eq, Sp,
            Call("topologicalClosure", subspace), Dot));
    }
}
