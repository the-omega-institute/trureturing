using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteSubspaceComplementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two line segments join points in an open convex set while avoiding finitely many subspaces of codimension at least two.",
        H("Path connected complements of finite subspace families"),
        Blocks(Describe.Lean(
            DescribeId.Create("open-convex-complement-finite-subspaces"),
            DeclarationHandle.Create(
                "D5/S3/Topology/FiniteSubspaceComplement.pathConnected_complement_in_open_convex"),
            H("Avoiding finitely many subspaces in an open convex set"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let E be a finite-dimensional real normed space and U a nonempty open convex subset. "
                        + "The family P of linear subspaces of E has a finite index type. Assume that for "
                        + "each member P and each vector x, adding the line spanned by x to P gives a proper "
                        + "subspace of E. This expresses the codimension condition using subspace sums.")),
                Paragraph(Text(
                    "For any two endpoints in U outside the forbidden subspaces, exclude the subspaces obtained "
                        + "by adjoining either endpoint to each forbidden subspace. Each enlarged subspace "
                        + "is proper and closed, so its complement is dense and open. Their finite intersection "
                        + "meets U. Join both endpoints to a point in this intersection. If either segment "
                        + "met a forbidden subspace away from its original endpoint, solving its affine "
                        + "combination for the intermediate point would place that point in an enlarged subspace."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula space = F.Id("E");
        Formula indices = F.Id("J");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula domain = F.Id("U");
        Formula family = F.Id("P");
        Formula index = F.Id("i");
        Formula vector = F.Id("x");
        Formula fiber = Call("P", index);
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Forall, Sp, space, Comma, indices, Colon, type, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", space), CloseBracket, Sp,
            OpenBracket, Call("NormedSpace", real, space), CloseBracket, RowBreak, Grp(),
            OpenBracket, Call("FiniteDimensional", real, space), CloseBracket, Sp,
            OpenBracket, Call("Finite", indices), CloseBracket, Comma, RowBreak,
            Forall, Sp, domain, Colon, Call("Set", space), Comma, Sp,
            family, Colon, new Formula.TypeArrow(indices, Call("Submodule", real, space)), Comma, RowBreak,
            Call("IsOpen", domain), Sp, Land, Sp, Call("Convex", real, domain), Sp, Land, Sp,
            Call("Nonempty", domain), Sp, Land, Sp, Open, Forall, Sp, index, Colon, indices, Comma, Sp,
            Forall, Sp, vector, Colon, space, Comma, Sp,
            Call("sup", fiber, Call("span", vector)), Sp, Neq, Sp, Call("top", space), Close,
            Sp, Rightarrow, RowBreak,
            Call("IsPathConnected", Call("diff", domain, Call("union", family))),
            End, Grp(F.Id("gathered"))));
    }
}
