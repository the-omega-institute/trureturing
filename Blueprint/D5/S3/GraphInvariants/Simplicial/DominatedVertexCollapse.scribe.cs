using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.GraphInvariants.Simplicial;

internal sealed class DominatedVertexCollapseDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deleting a dominated vertex of a finite simplicial complex is a relative collapse.",
        H("Relative dominated-vertex collapse"),
        Blocks(
            Definition("deletion", "deletion", "Deleting a simplex",
                "The deletion of a finite vertex set consists of the original faces that "
                + "do not contain that set. Faces are nonempty finite sets. Deleting a "
                + "singleton therefore retains exactly the faces avoiding its vertex."),
            Definition("free-pair", "IsFreePair", "A free face and its unique proper coface",
                "Both faces belong to the complex, the lower face is properly contained "
                + "in the upper face, and every face containing the lower one equals "
                + "one of these two. Thus removing the pair leaves a subcomplex."),
            Definition("elementary-collapse", "ElementaryCollapsesTo", "One elementary collapse",
                "There is a free pair whose lower-face deletion is exactly the endpoint. "
                + "The four definitions follow TauCetiProject/TauCeti at revision "
                + "64bb4d871548995899dee90beda88b787fafe27d, in LinkStar, "
                + "ElementaryCollapse and Collapse/Basic. The Tau Ceti contributors' "
                + "Apache 2.0 license is retained in "
                + "docs/reports/polarization-suppliers/tauceti-LICENSE.txt."),
            Definition("finite-collapse", "CollapsesTo", "Finite collapse sequences",
                "The reflexive transitive closure of elementary collapse allows a "
                + "finite sequence of moves, including the empty sequence."),
            Describe.Lean(
                DescribeId.Create("dominated-vertex-deletion"),
                DeclarationHandle.Create(Prefix + "collapsesTo_deletion_of_vertex_domination"),
                H("A dominated vertex can be deleted by elementary collapses"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The ambient vertex type is arbitrary, and only the face family "
                        + "is finite. Distinct vertices v and w satisfy domination when "
                        + "adjoining w to every face containing v gives another face. "
                        + "No face containing v is required to exist; the empty complex "
                        + "and an absent v give an empty collapse sequence.")),
                    Paragraph(Text(
                        "Among faces containing v and avoiding w, choose an inclusion "
                        + "maximal face A. A coface avoiding w equals A by maximality. "
                        + "A coface containing w has a nonempty face obtained by erasing "
                        + "w; maximality identifies that face with A. Thus the only "
                        + "proper coface is the face obtained by adjoining w.")),
                    Paragraph(Text(
                        "Deleting this free pair preserves domination and preserves "
                        + "the final deletion of v. The number of faces strictly "
                        + "decreases, so induction supplies a finite sequence. If no "
                        + "eligible face remains, even the singleton at v is absent. "
                        + "Every face avoiding v survives every move.")),
                    Paragraph(Text(
                        "For the independence complex of the path on N plus three "
                        + "vertices, with N at least one, use the one-based labels "
                        + "v equal to N plus one and w equal to N plus three. A face "
                        + "containing v avoids N plus two, the only neighbour of w, "
                        + "so the domination condition holds. On Fin of N plus three "
                        + "the same labels are N and N plus two. This gives the "
                        + "collapse to the exact deletion of v. Identifying that "
                        + "deletion with a join, transferring collapse to geometric "
                        + "realization, and deriving suspension and the classification "
                        + "by residue modulo three are separate assertions. The empty "
                        + "geometric realization is distinct from the empty "
                        + "probability pattern, and no physical operation follows "
                        + "from the combinatorial statement."))),
                DescribeRole.Theorem)), []));

    private static DocumentBlock Definition(string id, string declaration,
        string title, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/GraphInvariants/tauceti2026simplicialcollapse")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Implies(Formula premise, Formula conclusion) =>
        Seq(Open, premise, Close, Sp, Rightarrow, Sp, conclusion);
    private static Formula Member(Formula item, Formula family) =>
        Seq(item, Sp, InMacro, Sp, family);

    private static Formula MainFormula()
    {
        Formula vertexType = F.Id("V");
        Formula complex = F.Id("K");
        Formula lower = F.Id("A");
        Formula vertex = F.Id("v");
        Formula partner = F.Id("w");
        Formula domination = All("A", Call("Finset", vertexType),
            Implies(Member(lower, complex), Implies(Member(vertex, lower),
                Member(Call("insert", partner, lower), complex))));
        Formula endpoint = Call("deletion", complex,
            Seq(OpenBrace, vertex, CloseBrace));
        return Disp(All("V", F.Id("Type"),
            Seq(OpenBracket, Call("DecidableEq", vertexType), CloseBracket, Sp,
                All("K", Call("PreAbstractSimplicialComplex", vertexType),
                    Implies(Call("Finite", Call("faces", complex)),
                        All("v", vertexType, All("w", vertexType,
                            Implies(Seq(vertex, Sp, Neq, Sp, partner),
                                Implies(domination, Call("CollapsesTo", complex, endpoint))))))))));
    }
}
