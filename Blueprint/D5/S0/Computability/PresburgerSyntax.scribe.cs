using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability;

internal sealed class PresburgerSyntaxDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer affine coordinates and Boolean atoms have total executable semantics.", H("Integer affine expressions and formulas"),
        Blocks(Paragraph(Text("An Affine is an integer constant and a finite coefficient list. Its value is the constant plus the recursive dot product with a valuation list. The dot product stops when either list ends, so missing coefficients and missing valuation entries contribute zero. Coefficient addition retains the unmatched suffix; negation and scaling map the coefficients and change the constant.")),
            Paragraph(Text("Atoms express zero less than or equal to an affine value, divisibility by a positive natural modulus, or its negation. The positivity proof is part of the divisibility constructor. Atom.eval and QF.eval return Bool; QF has truth, falsity, atoms, conjunction, disjunction and negation. An empty atom conjunction and an empty formula conjunction are true; an empty disjunction is false.")),
            Paragraph(Text("Formula adds integer existential quantification to the Boolean constructors. Formula.holds is a proposition; its existential case conses the newly bound integer onto the valuation. Formula.all is the derived not-exists-not constructor. Sentence is an abbreviation of Formula, and evaluating at the empty valuation supplies the sentence convention. These syntax and arithmetic laws are supplied by ProveIt.")),
            Describe.Lean(DescribeId.Create("eval-add"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerSyntax.eval_add"),
            H("Affine addition preserves values"), StatementSource.FromAuthor(F.Disp(A("s", V("Affine"), A("t", V("Affine"), A("xs", Call("List", V("Int")), E(Call("eval", Call("add", V("s"), V("t")), V("xs")), Add(Call("eval", V("s"), V("xs")), Call("eval", V("t"), V("xs"))))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("Induction on coefficient lists proves dot_coeffAdd. Arithmetic distribution then gives the displayed identity. The companion laws eval_neg, eval_scale and eval_const state respectively negation, scalar multiplication and constant evaluation; eval_consCoeff at x::xs is a*x plus the tail value."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eval-conjunction"),
            DeclarationHandle.Create("D5/S0/Computability/PresburgerSyntax.eval_conjunction"),
            H("Finite conjunction is list.all"), StatementSource.FromAuthor(F.Disp(A("as", Call("List", V("Atom")), A("xs", Call("List", V("Int")), E(Call("eval", Call("conjunction", V("as")), V("xs")), Call("all", V("as"), Call("at", V("xs")))))))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Computability/reshetnikov2026presburger")), Blocks(Paragraph(Text("Here at(xs) is the function sending an atom a to Atom.eval a xs. Structural list induction includes the empty case. eval_disjunction replaces conjunction/all by disjunction/any, and eval_conjList applies the same all law to a list of QF formulas."))), DescribeRole.Theorem)), []));

    private static Formula V(string name) => F.Id(name);
    private static Formula A(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula E(Formula left, Formula right) => F.Seq(left, F.Sp, F.Eq, F.Sp, right);
}
