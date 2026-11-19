using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class CommonPositivePowersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/gouezel2026ietfreelistperiodicity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two finite words with equal positive natural powers commute.",
        H("Common Positive Powers Imply Commutation"),
        Blocks(Describe.Lean(
            DescribeId.Create("append-comm-of-flatten-replicate-eq"),
            DeclarationHandle.Create(
                "D5/S1/Words/Powers/CommonPositivePowers.append_comm_of_flatten_replicate_eq"),
            H("Equal positive powers imply word commutation"),
            StatementSource.FromAuthor(CommutationFormula()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text(
                    "For every universe level u, every alphabet type A in Type u, all finite "
                    + "words w and v over A, and natural numbers M and N with M nonzero and N "
                    + "nonzero, equality of flatten(replicate(M,w)) and flatten(replicate(N,v)) "
                    + "implies append(w,v)=append(v,w). The words may be empty. There is no "
                    + "finiteness, inhabitedness, ordering or decidable equality premise on A. "
                    + "Both nonzero assumptions are retained; no separate sharpness claim is made.")),
                Paragraph(Text(
                    "Four private helpers establish the period of a repeated word and "
                    + "reassemble blocks of a periodic word. The public theorem first handles "
                    + "empty words, then applies the Fine-Wilf gcd-period theorem to a doubled "
                    + "common power and expresses both words as powers of its initial gcd-length "
                    + "block. Addition of the exponents gives commutation. This is copied "
                    + "mathematical content from Sebastien Gouezel's IETFree/ListPeriodicity.lean "
                    + "at revision 48a23a630f39ae7c439b9efcbd03e729c18406fd, with four private "
                    + "helpers and one public theorem. Public visibility carries no discovery claim.")),
                Paragraph(Text(
                    "CyclicCentralizer consumes this theorem to show that positive-power roots "
                    + "of the same word commute. This supplier alone does not classify a "
                    + "centralizer or prove uniqueness of a generator. Its source notice, "
                    + "complete Apache 2.0 license reference and retirement condition against "
                    + "equivalent same-signature List declarations in this repository's own "
                    + "pinned Mathlib accompany the Lean source and primary software note."))),
            DescribeRole.Theorem))));

    private static Formula CommutationFormula()
    {
        var alphabet = F.Id("alpha");
        var words = Call("List", alphabet);
        var w = F.Id("w");
        var v = F.Id("v");
        var m = F.Id("M");
        var n = F.Id("N");
        var powersEqual = Equal(Call("flatten", Call("replicate", m, w)),
            Call("flatten", Call("replicate", n, v)));
        var commuting = Equal(Call("append", w, v), Call("append", v, w));
        var implication = Logic(NotEqual(m, D(0)), FormulaLogicOperator.Implies,
            Logic(NotEqual(n, D(0)), FormulaLogicOperator.Implies,
                Logic(powersEqual, FormulaLogicOperator.Implies, commuting)));
        return Disp(All("u", F.Id("Universe"),
            All("alpha", Call("Type", F.Id("u")),
                All("w", words, All("v", words,
                    All("M", Naturals(), All("N", Naturals(), implication)))))));
    }

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Logic(Formula left, FormulaLogicOperator operation, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), operation, Seq(Open, right, Close));
}
