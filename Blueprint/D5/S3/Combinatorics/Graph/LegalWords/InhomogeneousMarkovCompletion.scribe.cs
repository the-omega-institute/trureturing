using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LegalWords;

internal sealed class InhomogeneousMarkovCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LegalWords/InhomogeneousMarkovCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly interior site means determine a normalized hard-core binary path law, "
        + "and this law is unique among first-order Markov laws with those means.",
        H("Reconstructing a nonhomogeneous legal binary chain"),
        Blocks(
            Paragraph(Text(
                "A word is a Boolean function on a finite interval. The predicate Adm "
                + "requires that no two consecutive positions are both true. Indices "
                + "start at zero. The parameter n describes a path with n+2 sites, so "
                + "every path of length at least two occurs. A function u on the natural "
                + "numbers supplies the site means; only its first n+2 values are used. "
                + "Interior u N requires every used mean to lie strictly between zero "
                + "and one and every adjacent empty-empty remainder to be positive.")),
            Paragraph(Text(
                "The table site(u) assigns mass 1-u to false and u to true. In the order "
                + "false, true, the four entries of pair(u,v) are 1-u-v, v, u, and zero. "
                + "The transition step(u,v,a,b) divides the pair entry by site(u,a). "
                + "Strict interiority makes both denominators positive. Every transition "
                + "row sums to one, and propagating site(u) through this transition "
                + "gives site(v). The transitions can differ at every position.")),
            Paragraph(Text(
                "The function chain(q,K,m) assigns a word its initial mass q followed "
                + "by the product of its m transition entries. The function completion(u,n) "
                + "instead multiplies all n+1 adjacent pair entries and divides by the "
                + "product of the n internal site entries. The denominator removes the "
                + "second occurrence of each internal site. There is no endpoint "
                + "denominator. For n=0 the internal product is empty and equals one.")),
            Paragraph(Text(
                "LegalLaw m P means that P is nonnegative, sums to one over all "
                + "Boolean words of length m+1, and vanishes outside Adm. Means u m P "
                + "requires the probability of true at each position i to equal u(i). "
                + "The cylinder mass is the sum of P over words with an exact given "
                + "initial segment. Markov m P requires nonnegative stochastic rows "
                + "such that extending any history by a bit multiplies its cylinder "
                + "mass by the row entry at its last bit. On a history of positive "
                + "probability this entry is precisely the conditional probability "
                + "of the next bit. The equation also includes histories of zero "
                + "probability. Rows after the end of the path are unrestricted.")),
            Describe.Lean(DescribeId.Create("unique-markov-completion"),
                DeclarationHandle.Create(Prefix + "unique_markov_completion"),
                H("Existence, prescribed means, and uniqueness"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The overlapping-table expression is itself a legal probability "
                        + "law, has every prescribed site mean, and is first-order Markov. "
                        + "Every other legal first-order Markov law with these same means "
                        + "equals it as a function on all Boolean words. In particular "
                        + "the conclusion concerns a whole finite chain at arbitrary length, "
                        + "rather than only its adjacent pairs.")),
                    Paragraph(Text(
                        "Writing the overlapping-table quotient as an initial site "
                        + "mass times conditional transitions proves nonnegativity. "
                        + "Summing over the last bit removes one stochastic row. Repeating "
                        + "this operation gives every prefix marginal. The identity that "
                        + "a transition propagates one prescribed site table to the next "
                        + "then recovers all site means and normalization. A forbidden "
                        + "adjacent pair contributes a zero transition factor.")),
                    Paragraph(Text(
                        "The cylinder extension equations are equivalent to first-order "
                        + "factorization, by induction on the prefix length. For uniqueness, "
                        + "restrict any such law to prefixes. "
                        + "The full-law means identify both states of each prefix endpoint. "
                        + "Legal support makes the true-true adjacent mass zero. Positive "
                        + "true marginal therefore forces the true-true transition to "
                        + "vanish, and its row sum forces the true-false transition to "
                        + "equal one. The next mean identifies the false-true transition; "
                        + "its row sum supplies the last entry. Thus every transition "
                        + "and the initial table are fixed, determining the complete law.")),
                    Paragraph(Text(
                        "Strict interiority excludes zero site marginals and zero seams. "
                        + "The statement does not extend this quotient to boundary means. "
                        + "It also does not assert that a general legal law is Markov: "
                        + "uniqueness is restricted to the stated first-order class."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Statement()
    {
        Formula u = F.Id("u"), n = F.Id("n"), p = F.Id("P");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula words = new Formula.TypeArrow(Call("Fin", Add(n, D(2))), Call("Bool"));
        Formula laws = new Formula.TypeArrow(words, real);
        Formula count = Add(n, D(1));
        Formula law = Call("completion", u, n);
        Formula uniqueness = All("P", laws,
            Imp(Call("LegalLaw", count, p), Imp(Call("Means", u, count, p),
                Imp(Call("Markov", count, p), Eq(p, law)))));
        return All("u", new Formula.TypeArrow(nat, real), All("n", nat,
            Imp(Call("Interior", u, Add(n, D(2))),
                And(Call("LegalLaw", count, law), And(Call("Means", u, count, law),
                    And(Call("Markov", count, law), uniqueness))))));
    }
}
