using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class CyclicCentralizerDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Automata/lothaire1983words");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classify the full centralizer of a nonempty finite word by its unique nonempty generator.",
        H("A Unique Generator for a Word Centralizer"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-unique-centralizer-root"),
            DeclarationHandle.Create(
                "D5/S1/Words/Powers/CyclicCentralizer.exists_unique_centralizer_root"),
            H("The full centralizer has exactly one nonempty word generator"),
            StatementSource.FromAuthor(ClassificationFormula()),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text(
                    "For every universe level ell, every alphabet type A in Type ell, and every "
                    + "nonempty finite word w over A, there is exactly one nonempty word r such "
                    + "that every finite word v commutes with w exactly when v is a natural "
                    + "power of r. The displayed formula expands unique existence into existence "
                    + "and equality of every competing generator. It therefore specifies the "
                    + "literal list r, not just its length or a pairwise common power.")),
                Paragraph(Text(
                    "The operation append is list concatenation, nil is the empty list, and "
                    + "wordPower(n,r) is the concatenation of n copies of r. The quantifier on "
                    + "v includes nil, and n=0 supplies that commuting word. There is no "
                    + "Finite, Fintype, ordering, inhabitedness, or DecidableEq premise on A. "
                    + "For an empty alphabet there is no nonempty input w; infinite alphabets "
                    + "are included without a change of statement.")),
                Paragraph(Text(
                    "Choose a positive-power root r of w with least positive length. The "
                    + "public Fine-Wilf supplier CommonPositivePowers.append_comm_of_flatten_replicate_eq shows that "
                    + "any two positive-power roots of this same w commute. The public theorem "
                    + "CommutingWords.commute_iff_common_power then writes r and any such root "
                    + "s as powers of a common t. Nested list replication makes t a "
                    + "positive-power root of w. Minimality and the nonzero length of t force "
                    + "the exponent expressing r to be one. Hence every such s is a power of r. "
                    + "Applying the pairwise theorem to w and an arbitrary commuting v now "
                    + "puts all commuting words in this single generated monoid.")),
                Paragraph(Text(
                    "If another nonempty word s generates the same centralizer, r and s "
                    + "are powers of each other. Their positive lengths force both exponents "
                    + "to be one, giving s=r. Lothaire's hosted Chapter 1, Section 1.3, "
                    + "Proposition 1.3.2, p. 7, gives the centralizer statement; the nonempty "
                    + "uniqueness sentence of Proposition 1.3.1 gives the primitive-root "
                    + "interpretation. These locators use the hosted chapter version, not "
                    + "unchecked pagination in another edition.")),
                Paragraph(Text(
                    "The separate CommonPositivePowers module contains four private period "
                    + "and reassembly helpers and the public theorem "
                    + "append_comm_of_flatten_replicate_eq, an Apache 2.0 transplant from "
                    + "Sebastien Gouezel's IETFree/ListPeriodicity.lean at immutable revision "
                    + "48a23a630f39ae7c439b9efcbd03e729c18406fd. Both positive-exponent "
                    + "hypotheses and the original proof mechanism are retained. The source "
                    + "notice, complete license, immutable locator, and retirement condition "
                    + "against this repository's pinned Mathlib accompany the source and "
                    + "the literature note. No prefix-comparison or group code is included."))),
            DescribeRole.Theorem))));

    private static Formula ClassificationFormula()
    {
        var alphabet = F.Id("A");
        var words = Call("List", alphabet);
        var w = F.Id("w");
        var r = F.Id("r");
        var s = F.Id("s");
        var unique = All("s", words,
            Logic(Generator(w, s, words), FormulaLogicOperator.Implies, Equal(s, r)));
        var existence = ExistsF("r", words,
            Logic(Generator(w, r, words), FormulaLogicOperator.And, unique));
        return Disp(All("ell", F.Id("Universe"),
            All("A", Call("Type", F.Id("ell")),
                All("w", words,
                    Logic(NotEqual(w, Nil()), FormulaLogicOperator.Implies, existence)))));
    }

    private static Formula Generator(Formula w, Formula r, Formula words)
    {
        var v = F.Id("v");
        var n = F.Id("n");
        var powers = ExistsF("n", Naturals(), Equal(v, Call("wordPower", n, r)));
        var commuting = Equal(Call("append", w, v), Call("append", v, w));
        return Logic(NotEqual(r, Nil()), FormulaLogicOperator.And,
            All("v", words, Logic(commuting, FormulaLogicOperator.Iff, powers)));
    }

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula ExistsF(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Nil() => Call("nil");

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Logic(Formula left, FormulaLogicOperator operation, Formula right) =>
        new Formula.Logic(Seq(Open, left, Close), operation, Seq(Open, right, Close));
}
