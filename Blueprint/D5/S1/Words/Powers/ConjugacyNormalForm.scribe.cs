using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Powers;

internal sealed class ConjugacyNormalFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classify every conjugating word by a unique literal exponent and short cut.",
        H("The Unique Short-Cut Normal Form for Word Conjugacy"),
        Blocks(Describe.Lean(
            DescribeId.Create("unique-short-cut-normal-form"),
            DeclarationHandle.Create(
                "D5/S1/Words/Powers/ConjugacyNormalForm.conjugacy_iff_exists_unique_short_cut"),
            H("A fixed conjugating word determines the entire normal-form triple"),
            StatementSource.FromAuthor(ClassificationFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every universe u, every alphabet A in Type u, and all finite words "
                    + "a, b and z over A with a nonempty, the equation append(a,z)=append(z,b) "
                    + "holds exactly when there is a unique triple (n,p,q) satisfying "
                    + "a=append(p,q), b=append(q,p), z=append(wordPower(n,a),p) and "
                    + "length(p)<length(a). Uniqueness compares every competing exponent, "
                    + "prefix and suffix for these same a, b and z. It does not assert a "
                    + "unique cut from a and b alone.")),
                Paragraph(Text(
                    "Words are ordinary List A values. Concatenation is List.append, and "
                    + "wordPower(n,a) is the existing flatten(replicate(n,a)); no new word "
                    + "carrier or power operation is introduced. The alphabet needs no "
                    + "finiteness, order, inhabitedness or decidable equality. Empty and "
                    + "infinite alphabets remain quantified. Zero exponents, empty z and "
                    + "empty p are included. The short-cut inequality and a=pq force q "
                    + "nonempty, and hence b nonempty; neither is an additional premise. "
                    + "The word a need not be primitive.")),
                Paragraph(Text(
                    "Omega.FreeMonoid.Conjugacy supplies the reusable mathematics for an "
                    + "arbitrary carrier with associative concatenation, left identity and "
                    + "cancellation, additive natural length, length-directed prefix "
                    + "splitting, and the zero and successor power equations. These are "
                    + "elementary operation laws, with no classification hypothesis. "
                    + "If z is at least as long as a, prefix splitting removes one complete "
                    + "a and produces a strictly shorter conjugating word. Strong induction "
                    + "therefore reaches a short prefix. If z is already short, splitting "
                    + "produces its complementary suffix directly, with exponent zero.")),
                Paragraph(Text(
                    "For uniqueness, cancel complete initial copies of a from two power "
                    + "representations. A zero exponent cannot match a positive exponent "
                    + "because a short prefix cannot start with an entire a. Thus the "
                    + "exponents and literal short prefixes agree. Cancellation in the two "
                    + "factorizations of a then identifies the suffixes. A separate induction "
                    + "proves the converse conjugacy equation for every normal form.")),
                Paragraph(Text(
                    "The List interpretation proves every operation law, transports strict "
                    + "and ordinary natural numbers in both directions, and proves equivalence "
                    + "of the abstract normal predicate with all four displayed List clauses. "
                    + "The D5 declaration is the publication citation for this entry; its "
                    + "mathematics belongs to Omega.FreeMonoid.Conjugacy. It uses the proved "
                    + "existence, soundness and uniqueness results without repeating their "
                    + "length-descent proof.")),
                Paragraph(Text(
                    "Karhumaki's TUCS TR645, Section 5, Example 5, printed p. 12 / PDF p. 16, "
                    + "states the classical general solution x=rs, y=sr, z=r(sr)^i for i>=0. "
                    + "The identity (rs)^i r=r(sr)^i relates its convention to the displayed "
                    + "one. The report starts with a finite alphabet and does not state this "
                    + "fixed-z unique short-cut normalization. The arbitrary-alphabet scope "
                    + "and whole-triple uniqueness are proved here. The linked source note "
                    + "records that boundary; no original mathematical novelty is claimed.")),
                Paragraph(Ref("D5/L/Automata/karhumaki2004words"))),
            DescribeRole.Theorem))));

    private static Formula ClassificationFormula()
    {
        var words = Call("List", F.Id("A"));
        var a = F.Id("a");
        var b = F.Id("b");
        var z = F.Id("z");
        var n = F.Id("n");
        var p = F.Id("p");
        var q = F.Id("q");
        var competitor = All("m", Naturals(), All("r", words, All("s", words,
            Logic(Normal(a, b, z, F.Id("m"), F.Id("r"), F.Id("s")),
                FormulaLogicOperator.Implies,
                And(Equal(F.Id("m"), n), And(Equal(F.Id("r"), p), Equal(F.Id("s"), q)))))));
        var unique = ExistsF("n", Naturals(), ExistsF("p", words, ExistsF("q", words,
            And(Normal(a, b, z, n, p, q), competitor))));
        return Disp(All("u", F.Id("Universe"), All("A", Call("Type", F.Id("u")),
            All("a", words, All("b", words, All("z", words,
                Logic(NotEqual(a, Call("nil")), FormulaLogicOperator.Implies,
                    Logic(Equal(Call("append", a, z), Call("append", z, b)),
                        FormulaLogicOperator.Iff, unique))))))));
    }

    private static Formula Normal(Formula a, Formula b, Formula z, Formula n, Formula p, Formula q) =>
        And(Equal(a, Call("append", p, q)), And(Equal(b, Call("append", q, p)),
            And(Equal(z, Call("append", Call("wordPower", n, a), p)),
                new Formula.Relation(Call("length", p), FormulaRelationOperator.LessThan, Call("length", a)))));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ExistsF(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Logic(Formula a, FormulaLogicOperator operation, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), operation, Seq(Open, b, Close));
}
