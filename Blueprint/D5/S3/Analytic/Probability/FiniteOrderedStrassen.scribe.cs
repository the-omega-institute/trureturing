using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class FiniteOrderedStrassenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Probability/FiniteOrderedStrassen.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/atlas2026strassencoupling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-poset upper-set inequalities characterize ordered nonnegative couplings of equal-mass functions.",
        H("Finite ordered Strassen coupling"), Blocks(
            Paragraph(Text("Let alpha be any finite partial order, including the empty carrier. The real functions p and q are pointwise nonnegative and have equal total mass; that mass can be zero and is not normalized to one. An upper finset U contains every y above any x in U. A coupling is a nonnegative matrix whose row and column sums are exactly p and q and whose entries vanish unless x <= y.")),
            Describe.Lean(
                DescribeId.Create("forall-is-upper-set-sum-le-iff-exists-coupling"),
                DeclarationHandle.Create(Prefix + "forall_isUpperSet_sum_le_iff_exists_coupling"),
                H("Upper-set inequalities if and only if an ordered coupling exists"),
                StatementSource.FromAuthor(Disp(Telescope(
                    IffOf(
                        All("U", Call("Finset", A),
                            Imp(All("x", A, All("y", A,
                                    Imp(Member(V("x"), V("U")),
                                        Imp(Le(V("x"), V("y")), Member(V("y"), V("U")))))),
                                Le(SumIn("x", V("U"), Call("p", V("x"))),
                                   SumIn("x", V("U"), Call("q", V("x")))))),
                        Some("pi", new Formula.TypeArrow(A, new Formula.TypeArrow(A, Real)),
                            And(All("x", A, All("y", A, Le(D(0), Call("pi", V("x"), V("y"))))),
                                And(All("x", A, Eqn(SumOver("y", Call("pi", V("x"), V("y"))), Call("p", V("x")))),
                                    And(All("y", A, Eqn(SumOver("x", Call("pi", V("x"), V("y"))), Call("q", V("y")))),
                                        All("x", A, All("y", A,
                                            Imp(Seq(Neg, Sp, Par(Le(V("x"), V("y")))),
                                                Eqn(Call("pi", V("x"), V("y")), D(0))))))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The hard direction follows the retained ATLAS proof by strong induction on a finite-carrier measure combining carrier size with the counts of nonzero p and q entries. Zero p-mass on the carrier forces zero q-mass by nonnegativity and equal totals, and the zero matrix settles this case, including the empty carrier.")),
                    Paragraph(Text("If a nonempty proper upper set U is tight, with equal p- and q-mass on U, restrict both functions to U and to its complement in the carrier. An upper set V of the complement gives an upper set V union U of the original carrier; subtracting the tight equality transfers the inequality to V. Both subcarriers are smaller. Add their couplings to recover the original marginals and support.")),
                    Paragraph(Text("When there is no such tight cut, choose a with p(a) > 0. The upper cone of a and its inequality give b >= a with q(b) > 0. Moving t units from p(a) and q(b) preserves every upper-set inequality precisely when t does not exceed the slack of each upper set containing b but not a. If the smallest relevant slack is below min(p(a),q(b)), push that amount to make a nonempty proper upper cut tight and split there. Otherwise push min(p(a),q(b)); at least one nonzero support entry disappears, decreasing the induction measure. Adding t back at (a,b) restores the original marginals and order support.")),
                    Paragraph(Text("For the converse, order support makes every row starting in an upper set stay inside that set. Sum the row identities over U, commute the finite sums, and bound the restricted column sums by the full q columns using entrywise nonnegativity. The theorem imposes no unit-mass, nonempty-carrier, linear-order or Boolean-configuration restriction, and asserts no martingale condition or algorithm.")),
                    Paragraph(Text("This is a native integration of a known classical result from the immutable ATLAS Lean source, not a new mathematical theorem. The source and license correspondence, scope of the narrow transplant, and adopted-pin retirement condition are recorded in the Library note. Possible finite Markov and configuration uses have not been measured or completed here."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula A => V("alpha");
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type) => Seq(OpenBracket, type, CloseBracket, Sp);
    private static Formula Eqn(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Le(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Member(Formula value, Formula set) => Seq(value, Sp, InMacro, Sp, set);
    private static Formula Imp(Formula premise, Formula result) => Seq(Par(premise), Sp, Rightarrow, Sp, result);
    private static Formula And(Formula left, Formula right) => Seq(Par(left), Sp, Land, Sp, Par(right));
    private static Formula IffOf(Formula left, Formula right) => Seq(Par(left), Sp, Iff, Sp, Par(right));
    private static Formula SumOver(string index, Formula term) =>
        Seq(new Formula.Subscript(Sum, Seq(V(index), Colon, Sp, A)), Sp, Par(term));
    private static Formula SumIn(string index, Formula set, Formula term) =>
        Seq(new Formula.Subscript(Sum, Seq(V(index), Sp, InMacro, Sp, set)), Sp, Par(term));
    private static Formula Telescope(Formula body) =>
        All("alpha", Seq(V("Type"), Star),
            Seq(Inst(Call("Fintype", A)), Inst(Call("PartialOrder", A)),
                All("p", new Formula.TypeArrow(A, Real),
                    All("q", new Formula.TypeArrow(A, Real),
                        Imp(All("x", A, Le(D(0), Call("p", V("x")))),
                            Imp(All("x", A, Le(D(0), Call("q", V("x")))),
                                Imp(Eqn(SumOver("x", Call("p", V("x"))),
                                        SumOver("x", Call("q", V("x")))), body)))))));
}
