using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Raney;

internal sealed class MaximalBlockEvolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Raney/MaximalBlockEvolution.";
    private static readonly LibraryNoteRef Bks =
        LibraryNoteRef.Create("D5/L/Words/bugeaudkriegershallit2009morphic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A support-stabilized uniform morphism gives boundary-safe predecessor and successor control for actual maximal blocks.",
        H("Maximal-Block Evolution in a Uniform Fixed Word"),
        Blocks(
            Paragraph(Text(
                "Let A be a finite alphabet, mu a P-uniform morphism, w its pointwise fixed word, "
                    + "and Delta a finite set of letters. Bugeaud, Krieger, and Shallit provide "
                    + "the support-stabilization and inverse/image mechanism. This owner records "
                    + "the repository's exact natural-indexed, boundary-safe specialization. "
                    + "In particular, an interval starting at zero is maximal without reading w(-1).")),
            Node("morphismPower", "Literal iteration of a word morphism", MorphismPowerFormula(),
                "The zero iterate returns the input word. The successor iterate first applies the previous "
                    + "iterate and then flat-maps mu. This orientation is used unchanged when one stabilizing "
                    + "power is promoted to the downstream uniform morphism.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Bks)),
            Node("exists_support_stabilizing_power", "A positive power stabilizes every letter support",
                SupportFormula(),
                "BKS Lemma 10 is formalized for an arbitrary finite decidable alphabet. Iteration of the "
                    + "support map on the finite powerset eventually repeats. Choosing a positive multiple "
                    + "beyond the preperiod makes the selected support idempotent, so for every letter a and "
                    + "every positive n the supports of mu^(q*n)(a) and mu^q(a) agree.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Bks)),
            Node("uniformLetter", "A letter at a uniform-image offset", UniformLetterFormula(),
                "For offset t in Fin(P), uniformity proves that t is a valid index of mu(a). The definition "
                    + "returns that literal list entry; it adds no cyclic or padded indexing convention.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Bks)),
            Node("IsMaximalDeltaInterval", "Actual finite maximal intervals", MaximalFormula(),
                "An interval [first,last] is nonempty, every included word value lies in Delta, the right "
                    + "neighbor lies outside Delta, and either first is zero or its predecessor lies outside. "
                    + "The disjunction is the exact start-zero correction needed for an infinite word indexed "
                    + "by natural numbers.", DescribeRole.Definition, AssessedProvenance.FromRepo(Bks)),
            Node("uniform_bks11_predecessor", "A long late block has a bounded predecessor core",
                PredecessorFormula(),
                "Assume P>1, a P-uniform pointwise fixed word, two-step support equal to one-step support, an "
                    + "actual maximal Delta interval, first>P, and length>2P^2. Writing s=first/P and t=last/P, "
                    + "the central source interval [s+P,t-P] is nonempty and lies in Delta. Complementary "
                    + "letters occur in [s-P,s+P-1] and [t-P+1,t+P]. Complete second-order image cells and "
                    + "support stability force the central membership. The widened endpoint ranges are a "
                    + "conservative repository adaptation of BKS Lemma 11.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Bks)),
            Node("uniform_bks12_successor", "A predecessor core returns to one actual successor",
                SuccessorFormula(),
                "Under P>1 and length>P^2, the image interval from P(first+P) through "
                    + "P(last-P+1)-1 lies in Delta. Complementary letters occur before and after it inside "
                    + "the displayed P-scaled neighborhoods. Those witnesses select a unique actual maximal "
                    + "Delta interval crossing the central image. This is the boundary-explicit uniform "
                    + "specialization of the BKS Lemma 12 mechanism.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Bks)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("raney-maximal-block-evolution-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LeF(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula NotMem(Formula a, Formula b) => Seq(Neg, Sp, Paren(Mem(a, b)));
    private static Formula And(params Formula[] xs) => Join(xs, Land);
    private static Formula Or(params Formula[] xs) => Join(xs, Lor);
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
    private static Formula At(Formula w, Formula n) => new Formula.Apply(w, [n]);

    private static Formula MorphismPowerFormula() => Disp(new Formula.Aligned([
        Eqn(Call("morphismPower", V("mu"), D(0), V("x")), V("x")),
        Eqn(Call("morphismPower", V("mu"), Add(V("n"), D(1)), V("x")),
            Call("flatMap", Call("morphismPower", V("mu"), V("n"), V("x")), V("mu")))
    ]));

    private static Formula SupportFormula() => Disp(Ex("q", N(), And(
        LtF(D(0), V("q")),
        All("a", V("A"), All("n", N(), Implies(LtF(D(0), V("n")),
            Eqn(Call("support", Call("morphismPower", V("mu"), Mul(V("q"), V("n")),
                    Call("singleton", V("a")))),
                Call("support", Call("morphismPower", V("mu"), V("q"),
                    Call("singleton", V("a")))))))))));

    private static Formula UniformLetterFormula() => Disp(Eqn(
        Call("uniformLetter", V("mu"), V("a"), V("t")),
        Call("get", Call("mu", V("a")), V("t"))));

    private static Formula MaximalFormula() => Disp(Seq(
        Call("IsMaximalDeltaInterval", V("Delta"), V("w"), V("i"), V("j")), Sp, Iff, Sp,
        Paren(And(LeF(V("i"), V("j")),
            Paren(All("n", N(), Implies(And(LeF(V("i"), V("n")), LeF(V("n"), V("j"))),
                Mem(At(V("w"), V("n")), V("Delta"))))),
            Paren(Or(Eqn(V("i"), D(0)), NotMem(At(V("w"), Sub(V("i"), D(1))), V("Delta")))),
            NotMem(At(V("w"), Add(V("j"), D(1))), V("Delta"))))));

    private static Formula PredecessorFormula() => Disp(Seq(
        Call("BKS11Hyp", V("P"), V("mu"), V("w"), V("Delta"), V("i"), V("j")),
        Sp, Rightarrow, Sp, Paren(And(
            LeF(Add(Call("div", V("i"), V("P")), V("P")),
                Sub(Call("div", V("j"), V("P")), V("P"))),
            Paren(All("n", N(), Implies(And(
                    LeF(Add(Call("div", V("i"), V("P")), V("P")), V("n")),
                    LeF(V("n"), Sub(Call("div", V("j"), V("P")), V("P")))),
                Mem(At(V("w"), V("n")), V("Delta"))))),
            Call("leftComplementWitness", V("P"), V("w"), V("Delta"), V("i")),
            Call("rightComplementWitness", V("P"), V("w"), V("Delta"), V("j"))))));

    private static Formula SuccessorFormula() => Disp(Seq(
        Call("BKS12Hyp", V("P"), V("mu"), V("w"), V("Delta"), V("i"), V("j")),
        Sp, Rightarrow, Sp, Paren(And(
            Call("centralImageInDelta", V("P"), V("w"), V("Delta"), V("i"), V("j")),
            Call("leftImageComplementWitness", V("P"), V("w"), V("Delta"), V("i")),
            Call("rightImageComplementWitness", V("P"), V("w"), V("Delta"), V("j")),
            Call("existsUniqueActualSuccessor", V("P"), V("w"), V("Delta"), V("i"), V("j"))))));
}
