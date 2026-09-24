using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Raney;

internal sealed class ZeroRunFamiliesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Raney/ZeroRunFamilies.";
    private static readonly LibraryNoteRef RaneySource =
        LibraryNoteRef.Create("D5/L/Recurrence/euhuangkao2026zerorun");
    private static readonly LibraryNoteRef BksSource =
        LibraryNoteRef.Create("D5/L/Words/bugeaudkriegershallit2009morphic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every admissible Raney sequence, nonzero residues occur arbitrarily far out and every actual maximal zero-run length lies in finitely many affine prime-power families.",
        H("Raney Zero-Run Coefficient Families"),
        Blocks(
            Paragraph(Text(
                "Eu, Huang, and Kao's Conjecture 7.1 asks for finite affine prime-power families containing "
                    + "the tied left-to-right record values of the actual zero-run sequence. The theorem here "
                    + "keeps the literal integral Raney quotient and proves the stronger statement for every "
                    + "actual maximal finite zero interval. Its separate unbounded-support conjunct rules out "
                    + "an infinite zero tail. It neither truncates to finite prefixes nor asserts that every "
                    + "coefficient-family term is realized.")),
            Node("raneyNumber", "The literal integral Raney number", RaneyNumberFormula(),
                "For natural k,r,n, raneyNumber(k,r,n) is the natural quotient "
                    + "r*binomial(k*n+r,n)/(k*n+r), exactly as in the source. The theorem assumes positive k and r. "
                    + "Its proof establishes the needed exact division identity before casting to ZMod(p); it does "
                    + "not divide by k*n+r in the residue field.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(RaneySource)),
            Node("raney_zero_run_coefficient_families", "All actual Raney zero runs have finite coefficient data",
                ResultFormula(),
                "Let k,r be positive and p prime with p not dividing k*r. First, for every cutoff there is n at "
                    + "least that cutoff with raneyNumber(k,r,n) nonzero modulo p. Second, one finite set C of "
                    + "integer triples (a,b,c), all with c>0, is chosen before arbitrary first and last. Every "
                    + "actual maximal zero interval satisfies c*(last+1-first)=a*p^m+b for some member of C and "
                    + "some natural m. Thus all tied record lengths belong to the required finite union.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(RaneySource, BksSource),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("raney-conjecture-7-1-zero-run-record-families"),
                    ResolutionKind.Proved),
                Paragraph(Text(
                        "The proof first derives a guarded adjacent-binomial identity. At n=0 the predecessor "
                            + "term is zero; for n>0 it proves that (k-1)*choose(k*n+r-1,n-1) is bounded by "
                            + "choose(k*n+r-1,n), and their natural difference equals the literal quotient. "
                            + "This supplies both integrality and the later residue readout.")),
                Paragraph(Text(
                        "Set A=max(k-1,r-1), State=Fin(A+1) x Bool, and Alphabet=State -> ZMod(p). The false "
                            + "Boolean component evaluates choose(k*n+a,n). The true component evaluates the "
                            + "guarded predecessor choose(k*n+a,n-1), with value zero at n=0. For a base-p digit "
                            + "d, the next index (k*d+a)/p remains in Fin(A+1). Lucas' theorem supplies the normal "
                            + "transition, the positive-digit predecessor transition, and the zero-digit borrow "
                            + "transition. The resulting list of p digit transforms is a p-uniform morphism, and "
                            + "the complete evaluation vector is its pointwise fixed word, including leading zeros.")),
                Paragraph(Text(
                        "At state r-1, the ordinary value minus (k-1) times the predecessor value is exactly the "
                            + "literal Raney residue. For sufficiently large j with r-1<p^(j-1), the Lucas readout "
                            + "at n=p^j reduces to k modulo p. Since p does not divide k*r, p does not divide k, "
                            + "so these arbitrarily large values are nonzero. Applying the generic actual-block "
                            + "coefficient theorem with Delta={0} proves the second conjunct.")),
                Paragraph(Text(
                        "The two conjuncts have distinct roles: arbitrarily large nonzero residues exclude a terminal "
                            + "infinite zero run, while one finite set C, chosen before the interval endpoints, covers "
                            + "all actual maximal finite zero intervals. This is a containment statement only: it "
                            + "does not assert that every coefficient triple or exponent yields an actual interval, "
                            + "and it supplies no converse realization theorem."))))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null, params DocumentBlock[] extra)
    {
        var proseBlocks = Blocks([Paragraph(Text(prose)), .. extra]);
        return Describe.Lean(
            DescribeId.Create("raney-zero-run-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, proseBlocks, role, resolution);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LeF(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula And(params Formula[] xs) => Join(xs, Land);
    private static Formula Implies(Formula a, Formula b) => Seq(Paren(a), Sp, Rightarrow, Sp, Paren(b));
    private static Formula Paren(Formula x) => Seq(Open, x, Close);
    private static Formula Join(Formula[] xs, Formula op)
    {
        Formula result = xs[0];
        for (var i = 1; i < xs.Length; i++) result = Seq(result, Sp, op, Sp, xs[i]);
        return result;
    }
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula RaneyNumberFormula() => Disp(All("k", N(), All("r", N(), All("n", N(), Eqn(
        Call("raneyNumber", V("k"), V("r"), V("n")),
        Call("NatDiv", Mul(V("r"), Call("choose", Add(Mul(V("k"), V("n")), V("r")), V("n"))),
            Add(Mul(V("k"), V("n")), V("r"))))))));

    private static Formula ResultFormula()
    {
        var hypotheses = And(LtF(D(0), V("k")), LtF(D(0), V("r")), Call("Prime", V("p")),
            Seq(Neg, Sp, Paren(Divides(V("p"), Mul(V("k"), V("r"))))));
        var unbounded = All("cutoff", N(), Ex("n", N(), And(LeF(V("cutoff"), V("n")),
            Seq(Call("castZMod", Call("raneyNumber", V("k"), V("r"), V("n")), V("p")),
                Sp, Neq, Sp, D(0)))));
        var positiveCoefficients = All("abc", Call("members", V("C")),
            LtF(D(0), Call("third", V("abc"))));
        var coveredIntervals = All("first", N(), All("last", N(), Implies(
            Call("IsMaximalDeltaInterval", Call("singleton", D(0)),
                Call("raneyResidue", V("k"), V("r"), V("p")), V("first"), V("last")),
            Ex("abc", Call("members", V("C")), Ex("m", N(), Eqn(
                Mul(Call("third", V("abc")), Sub(Add(V("last"), D(1)), V("first"))),
                Add(Mul(Call("first", V("abc")), Pow(V("p"), V("m"))),
                    Call("second", V("abc")))))))));
        var families = Ex("C", Call("Finset", Call("Prod", Z(), Z(), N())),
            And(Paren(positiveCoefficients), Paren(coveredIntervals)));
        var conclusion = And(Paren(unbounded), Paren(families));
        return Disp(All("k", N(), All("r", N(), All("p", N(),
            Implies(hypotheses, conclusion)))));
    }
}
