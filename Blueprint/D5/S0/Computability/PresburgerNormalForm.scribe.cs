using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class PresburgerNormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polarity conversion preserves Boolean evaluation, including nested negation.", H("Polarity and disjunctive normal form"),
        Blocks(Paragraph(Text("A Clause is a list of atoms interpreted by all; a DNF is a list of clauses interpreted by any. DNF.cross forms all concatenations of a clause from each input. Thus cross implements conjunction and append implements disjunction. The empty DNF is false, whereas the singleton empty clause is true.")),
            Paragraph(Text("Atom.negate changes zero<=t into zero<=-t-1. The minus one uses discreteness of integers: it expresses strict negativity without a new atom constructor. Divisibility and nondivisibility swap. DNF.ofPolarity pushes negation through every constructor; negative conjunction becomes appended negative branches and negative disjunction becomes a cross product. No assumption restricts the nesting of negation.")),
            Describe.Lean(DescribeId.Create("eval-negate"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerNormalForm.eval_negate"),
            H("Exact atom complement"), StatementSource.FromAuthor(F.Disp(A("a", V("Atom"), A("xs", Call("List", V("Int")), E(Call("eval", Call("negate", V("a")), V("xs")), Call("not", Call("eval", V("a"), V("xs")))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("Integer order separates the le case into nonnegative and negative values. The divisibility cases use Boolean complementation. This law feeds the negative atom branch of the polarity induction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eval-ofpolarity"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerNormalForm.eval_ofPolarity"),
            H("Positive and negative conversion"), StatementSource.FromAuthor(F.Disp(A("b", V("Bool"), A("p", V("QF"), A("xs", Call("List", V("Int")), E(Call("evalDNF", Call("ofPolarity", V("b"), V("p")), V("xs")), Call("if", V("b"), Call("eval", V("p"), V("xs")), Call("not", Call("eval", V("p"), V("xs")))))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("evalDNF denotes DNF.eval. Induction on p, generalized over b, combines eval_cross, eval_append and eval_negate. evalClause_append is Boolean conjunction of the two clauses. Finally eval_toQF states that rebuilding a disjunction of atom conjunctions preserves DNF.eval."))), DescribeRole.Theorem)), [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Computability/PresburgerSyntax"))]));

    private static Formula V(string name) => F.Id(name);
    private static Formula A(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula E(Formula left, Formula right) => F.Seq(left, F.Sp, F.Eq, F.Sp, right);
}
