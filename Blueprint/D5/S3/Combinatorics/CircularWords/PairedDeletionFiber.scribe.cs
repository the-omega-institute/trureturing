using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CircularWords;

internal sealed class PairedDeletionFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CircularWords/PairedDeletionFiber.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a fixed support of at least three labels, a pair of labelled circular deletions has a fibre of at most two: the source circle and, exactly when the deleted labels are adjacent, its adjacent swap.",
        H("Paired Circular Deletion Fibres"), Blocks(
            Paragraph(Text("Fix a finite support A and nodup oriented circles C,D with toFinset C = toFinset D = A. "
                + "For distinct support labels a,b, the labelled observations are the two residual circles delete a C and delete b C. "
                + "Choose one marker r in A minus {a,b}; rooting both rotation classes at r turns residual equality into equality of two anchored filtered lists.")),
            Describe.Lean(DescribeId.Create("paired-fibre"), DeclarationHandle.Create(Prefix + "paired_fiber_iff"),
                H("Necessary and sufficient classification"), StatementSource.FromAuthor(PairedFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The list proof is induction on the first nodup list. If both heads lie outside {a,b}, either erasure preserves the heads, forcing equal heads and a recursive tail classification. Equal a or b heads are fixed by the other erasure and nodup. Opposite heads force the tails to be b::R and a::R (or the symmetric form), so the full words differ exactly by an adjacent a,b swap. Rooted equality is converted with anchored_coe_injective, and the converse is the direct filter calculation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pair-fibre-bound"), DeclarationHandle.Create(Prefix + "pair_fiber_at_most_two"),
                H("At most two states in one fibre"), StatementSource.FromAuthor(BoundFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Choose one marker r outside the deleted pair and use it for C,D,E. The fixed-root classification makes every non-central fibre member the swap map of C by the same Equiv.swap a b. Hence two members different from C are equal. The result is stated for card A >= 3, which is the exact scope needed to choose the common root."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("paired-fibre-existence"), DeclarationHandle.Create(Prefix + "exists_nontrivial_alternative_iff_cyclicAdjacent"),
                H("A nontrivial alternative exists exactly at a cyclic adjacent cut"), StatementSource.FromAuthor(ExistenceFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For a supported nodup source circle, an actual second supported circle with the same two labelled deletions and different rotation class exists exactly when the two deleted labels occupy a cyclically adjacent pair. The witness includes every rooted cut, including the wrap-around cut: the source is r::P++[a,b]++Q or r::P++[b,a]++Q, and the constructed alternative reverses that adjacent block. The proof preserves nodup by the adjacent list permutation, support by the same permutation, proves both filtered deletion equalities, and rules out equality by anchored injectivity and a≠b."))),
                DescribeRole.Theorem),
            Paragraph(Text("The carrier identifies rotations and preserves orientation. The observations are paired residuals from the same source cycle. The statements concern exact finite objects; they make no marginal-law, noise-stability, or sample-complexity assertion.")))));

    private static Formula PairedFormula()
    {
        Formula t = F.Id("T"), A = F.Id("A"), a = F.Id("a"), b = F.Id("b"),
            C = F.Id("C"), Dd = F.Id("D");
        Formula supportedC = And(Call("Nodup", C), Eq(Call("toFinset", C), A));
        Formula supportedD = And(Call("Nodup", Dd), Eq(Call("toFinset", Dd), A));
        Formula obs = And(Eq(Call("delete", a, C), Call("delete", a, Dd)),
            Eq(Call("delete", b, C), Call("delete", b, Dd)));
        Formula swap = Ex("r", t, And(In(F.Id("r"), A),
            And(Ne(F.Id("r"), a), And(Ne(F.Id("r"), b),
                Call("adjacentSwapAt", F.Id("r"), a, b, C, Dd)))));
        Formula premise = And(Le(D(3), Call("card", A)), And(In(a, A), And(In(b, A),
            And(Ne(a, b), And(supportedC, supportedD)))));
        Formula body = Imp(premise, Iff(obs, Or(Eq(C, Dd), swap)));
        Formula quantified = All("A", Call("Finset", t), All("a", t, All("b", t,
            All("C", Call("Cycle", t), All("D", Call("Cycle", t), body)))));
        return WithType(quantified);
    }

    private static Formula BoundFormula()
    {
        Formula t = F.Id("T"), A = F.Id("A"), a = F.Id("a"), b = F.Id("b"),
            C = F.Id("C"), Dd = F.Id("D"), E = F.Id("E");
        Formula supportedC = And(Call("Nodup", C), Eq(Call("toFinset", C), A));
        Formula supportedD = And(Call("Nodup", Dd), Eq(Call("toFinset", Dd), A));
        Formula supportedE = And(Call("Nodup", E), Eq(Call("toFinset", E), A));
        Formula pairCD = And(Eq(Call("delete", a, C), Call("delete", a, Dd)),
            Eq(Call("delete", b, C), Call("delete", b, Dd)));
        Formula pairCE = And(Eq(Call("delete", a, C), Call("delete", a, E)),
            Eq(Call("delete", b, C), Call("delete", b, E)));
        Formula premise = And(Le(D(3), Call("card", A)), And(In(a, A), And(In(b, A),
            And(Ne(a, b), And(supportedC, And(supportedD,
                And(supportedE, And(pairCD, And(pairCE, And(Ne(Dd, C), Ne(E, C)))))))))));
        Formula conclusion = Eq(Dd, E);
        Formula quantified = All("A", Call("Finset", t), All("a", t, All("b", t,
            All("C", Call("Cycle", t), All("D", Call("Cycle", t),
                All("E", Call("Cycle", t), Imp(premise, conclusion)))))));
        return WithType(quantified);
    }

    private static Formula ExistenceFormula()
    {
        Formula t = F.Id("T"), A = F.Id("A"), a = F.Id("a"), b = F.Id("b"),
            C = F.Id("C"), Dd = F.Id("D");
        Formula supportedC = And(Call("Nodup", C), Eq(Call("toFinset", C), A));
        Formula alt = Ex("D", Call("Cycle", t), And(Call("Nodup", Dd),
            And(Eq(Call("toFinset", Dd), A), And(Ne(Dd, C),
                And(Eq(Call("delete", a, C), Call("delete", a, Dd)),
                    Eq(Call("delete", b, C), Call("delete", b, Dd)))))));
        Formula adjacency = Ex("r", t, And(In(F.Id("r"), A),
            And(Ne(F.Id("r"), a), And(Ne(F.Id("r"), b),
                Call("cyclicAdjacentAt", F.Id("r"), a, b, C)))));
        Formula premise = And(Le(D(3), Call("card", A)), And(In(a, A), And(In(b, A),
            And(Ne(a, b), supportedC))));
        Formula body = Imp(premise, Iff(alt, adjacency));
        Formula quantified = All("A", Call("Finset", t), All("a", t, All("b", t,
            All("C", Call("Cycle", t), body))));
        return WithType(quantified);
    }

    private static Formula WithType(Formula body) => Disp(All("T", Call("Type"),
        Seq(OpenBracket, Call("DecidableEq", F.Id("T")), CloseBracket, Sp, body)));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Ex(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Not(Seq(Open, Eq(x, y), Close));
    private static Formula In(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Seq(Open, x, Close), FormulaLogicOperator.And, Seq(Open, y, Close));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(Seq(Open, x, Close), FormulaLogicOperator.Or, Seq(Open, y, Close));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Seq(Open, x, Close), FormulaLogicOperator.Implies, Seq(Open, y, Close));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(Seq(Open, x, Close), FormulaLogicOperator.Iff, Seq(Open, y, Close));
}
