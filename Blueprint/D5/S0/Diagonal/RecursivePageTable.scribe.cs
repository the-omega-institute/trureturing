using static StrataLint.Scribe.DefinitionDsl;

using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class RecursivePageTableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var ordinary = Equal(
            Call("Walk", F.Id("lookup"), F.Id("root"),
                Call("list", F.Id("i"), F.Id("j"))),
            F.Id("data"));
        var introspection = Equal(
            Call("Walk", F.Id("lookup"), F.Id("root"),
                Call("list", F.Id("self"), F.Id("i"))),
            F.Id("leaf"));
        var closure = F.Seq(
            F.Forall, F.Sp, F.Id("L"), F.Comma, F.Sp,
            Equal(
                Call("Walk", F.Id("lookup"), F.Id("root"),
                    Call("replicate", F.Id("L"), F.Id("self"))),
                F.Id("root")));
        var conclusion = new Formula.Logic(
            ordinary,
            FormulaLogicOperator.And,
            new Formula.Logic(introspection, FormulaLogicOperator.And, closure));
        var assumptions = new Formula.Logic(
            Equal(Call("lookup", F.Id("root"), F.Id("self")), F.Id("root")),
            FormulaLogicOperator.Implies,
            new Formula.Logic(
                Equal(Call("lookup", F.Id("root"), F.Id("i")), F.Id("leaf")),
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    Equal(Call("lookup", F.Id("leaf"), F.Id("j")), F.Id("data")),
                    FormulaLogicOperator.Implies,
                    conclusion)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A self-mapped page-table root supports ordinary lookup, leaf introspection, and finite root closure.",
            H("Recursive Page-Table Walk"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("recursive-page-table-walk"),
                    DeclarationHandle.Create(
                        "D5/S0/Diagonal/RecursivePageTable.recursive_page_table_walk"),
                    H("Recursive page-table walk"),
                    StatementSource.FromAuthor(F.Disp(assumptions)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The lookup map consumes one index per dereference. The first two "
                                + "equalities follow by unfolding two steps: a root entry selects "
                                + "the leaf and the leaf entry selects the data, while the self-map "
                                + "slot sends the root back to itself.")),
                        Paragraph(Text(
                            "Induction on the number of repeated self-map indices proves the final "
                                + "equality, so every finite all-zero walk remains at the root."))),
                    DescribeRole.Theorem))));
    }
}
