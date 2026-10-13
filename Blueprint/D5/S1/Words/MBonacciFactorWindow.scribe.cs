using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class MBonacciFactorWindowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every factor of the actual m-bonacci word has an occurrence in an exact image-weight window.",
        H("An Exact Factor Window for the m-Bonacci Word"),
        Blocks(
            Paragraph(Text("Let m be at least two. The alphabet is Fin m. The substitution sends "
                + "a to [0,a+1] when a+1<m and sends m-1 to [0]. Write P_j for the jth "
                + "iterate on zero and U_m(j) for its length. The word u_m is the literal "
                + "infinite word obtained from these nested, unbounded iterates. A factor "
                + "at q of length n is the list u_m(q),...,u_m(q+n-1).")),
            Describe.Lean(
                DescribeId.Create("factor-window"),
                DeclarationHandle.Create("D5/S1/Words/MBonacciFactorWindow.factor_window"),
                H("Every start is represented by the bounded window"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Words/turek2013abelian")),
                Blocks(
                    Paragraph(Text("For all natural k and all positive n at most U_m(k), "
                        + "every factor starting at any natural q has an identical occurrence "
                        + "at some natural p at most U_m(k+m). Both endpoints are included: "
                        + "m=2 and n=U_m(k) satisfy the same statement.")),
                    Paragraph(Text("Every alphabet letter a appears in P_a, by following the "
                        + "successor in its image. Nested prefixes therefore place every letter "
                        + "in P_(m-1). Appending a reserved zero shows that each image phi(a) "
                        + "followed by zero is an infix of P_m followed by zero, including "
                        + "a terminal occurrence with no remaining source letters.")),
                    Paragraph(Text("Each (k+1)st image of a letter begins with P_k. Locate the "
                        + "start of the desired factor in a sufficiently long finite iterate, "
                        + "viewed as a concatenation of these images. A window of length at most "
                        + "|P_k| lies in its starting image followed by P_k. This also covers a "
                        + "window in the final block. Applying the kth substitution to the "
                        + "sentinel infix confines the window to P_(k+m) followed by P_k.")),
                    Paragraph(Text("This control word is an actual prefix. If the resulting "
                        + "occurrence starts at or before |P_(k+m)|, keep that start. Otherwise "
                        + "the whole window lies in the final P_k; subtract |P_(k+m)| and use "
                        + "the initial copy of P_k. Since P_k is a prefix of P_(k+m), the new "
                        + "start satisfies the exact non-strict bound."))),
                DescribeRole.Theorem),
            Paragraph(Text("The statement is the m-bonacci specialization of the cited "
                + "factor-containing prefix result, Observation 4.1 and Propositions 4.4 "
                + "and 4.8. Its F_k is U_m(k), and its prefix "
                + "u_[n] is factor(u_m,0,n). Observation 4.1 places each length-n factor "
                + "in phi^k(0t0), with no zero in t, including an empty t. Here the "
                + "substitution images between successive zeroes give the corresponding "
                + "sentinel blocks phi(a) followed by zero. Proposition 4.4 places these "
                + "blocks in the actual prefix P_R followed by zero. All substitution "
                + "exponents equal one: alpha_0=1 and the first positive index with "
                + "alpha_l at least one is l=1. Thus R=m+1-1=m, also for m=2.")),
            Paragraph(Text("With this R, Proposition 4.8 uses the factor-covering prefix "
                + "P_(k+m) followed by u_[n], of length U_m(k+m)+n. The proved bound "
                + "p at most U_m(k+m) puts every ordered factor wholly in that prefix. "
                + "The proof first uses the longer prefix P_(k+m) followed by P_k; a "
                + "window extending past its final n-letter prefix lies wholly in P_k "
                + "and can be moved to the initial copy. These are statements about "
                + "the literal word and its factors; they assert neither a minimal "
                + "window nor an optimal enumeration algorithm.")))));

    private static Formula Statement()
    {
        Formula m = F.Id("m"), k = F.Id("k"), n = F.Id("n"), q = F.Id("q"), p = F.Id("p");
        Formula word = Call("word", m);
        Formula equality = Eq(Call("factor", word, q, n), Call("factor", word, p, n));
        Formula occurrence = Ex("p", N(), And(Le(p, Call("U", m, Add(k, m))), equality));
        Formula everyStart = All("q", N(), occurrence);
        Formula sizeBound = Imp(Le(n, Call("U", m, k)), everyStart);
        Formula positiveLength = All("n", N(), Imp(Le(F.D(1), n), sizeBound));
        Formula everyScale = All("k", N(), positiveLength);
        return F.Disp(All("m", N(), Imp(Le(F.D(2), m), everyScale)));
    }

    private static Formula N() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Ex(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
