using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OrthogonalDeMorganDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal complementation exchanges joins and meets of closed subspaces.",
        H("Orthogonal De Morgan Identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("orthogonal-complements-exchange-joins-and-meets"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Algebra/OrthogonalDeMorgan.orthogonal_de_morgan"),
                H("Orthogonal complements exchange joins and meets"),
                StatementSource.FromAuthor(OrthogonalDeMorganFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k be a real-or-complex scalar field, E a complete inner-product "
                            + "space over k, and M and N closed subspaces. Orthogonal "
                            + "complementation sends the closed join of M and N to the meet of "
                            + "their orthogonal complements, and sends their meet to the closed "
                            + "join of their orthogonal complements.")),
                    Paragraph(Text(
                        "The join operation on ClosedSubmodule is the closure of the algebraic "
                            + "sum. Thus the second equality is exactly the source statement that "
                            + "the orthogonal complement of an intersection is the closure of the "
                            + "sum of the two orthogonal complements.")),
                    Paragraph(Text(
                        "Repository search found no D5 declaration of this pair of identities. "
                            + "The pinned Mathlib tree contains the exact declarations "
                            + "ClosedSubmodule.inf_orthogonal and "
                            + "ClosedSubmodule.sup_orthogonal, which are imported and applied "
                            + "directly. The ordered search stopped at this exact Mathlib hit, "
                            + "before third-party libraries."))),
                DescribeRole.Theorem))));

    private static Formula OrthogonalDeMorganFormula()
    {
        Formula scalar = F.Id("k");
        Formula space = F.Id("E");
        Formula left = F.Id("M");
        Formula right = F.Id("N");
        Formula Orthogonal(Formula subspace) => Call("orthogonal", subspace);
        Formula Join(Formula first, Formula second) => Call("join", first, second);
        Formula Meet(Formula first, Formula second) => Call("meet", first, second);

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
            left, Comma, Sp, right, Colon, Sp,
            Operatorname, Grp(F.Id("ClosedSubmodule")), Underscore, Grp(scalar),
            Open, space, Close, Comma, Esc,
            Orthogonal(Join(left, right)), Sp, Eq, Sp,
            Meet(Orthogonal(left), Orthogonal(right)), Sp, Land, Sp,
            Orthogonal(Meet(left, right)), Sp, Eq, Sp,
            Join(Orthogonal(left), Orthogonal(right)), Dot));
    }
}
