using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.Comparison;

internal sealed class RoundTripRankOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting Directions Have Rank One.",
        H("Commuting Directions Have Rank One"),
        Describe.Lean(
            DescribeId.Create("centralizer-line"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/Comparison/RoundTripRankOne.centralizer_line"),
            H("Commuting Directions Have Rank One"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Use the comparison data of RoundTripComparison: a complete finite-dimensional real normed associative unital algebra A, a commutator-closed real subspace L, a subgroup G containing its exponentials and preserving L by conjugation, and the bounded faithful conjugation-invariant function with duplication and symmetric quadratic germ h.")),
                Paragraph(Text("In the displayed formula, Data(L,G) is the Lean structure containing exactly the stated closure, boundedness, faithfulness, duplication, conjugation and symmetric quadratic-germ hypotheses. The anonymous Data(L,G) premise means that such comparison data are given; the conclusion does not otherwise depend on a choice of name for those data.")),
                Paragraph(Text("For every nonzero X in L and every Y in L satisfying [X,Y]=0, there is a real scalar c with Y=cX. In particular, every commuting pair is linearly dependent; if X=0 the latter conclusion is immediate.")),
                Paragraph(Text("The preceding metric theorem makes h an inner product. On the span of X and Y all elements commute, so the points whose exponentials are the identity form an additive subgroup. The exact cosine formula puts the entire h-sphere of radius sqrt(2)*pi in this kernel and excludes its sphere of half that radius. The spherical additive-kernel theorem therefore bounds the dimension of the span by one. Since X is nonzero it spans this space.")),
                Paragraph(Text("The norm induced by h is used only in this finite-dimensional geometric argument. The original quadratic-germ hypothesis remains in the inherited algebra norm; no equality between these norms is assumed. The conclusion concerns infinitesimal commuting directions and asserts no global group classification."))),
            DescribeRole.Theorem)));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string n, Formula ty, Formula p) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(n), ty)], p);
    private static Formula Ex(string n, Formula ty, Formula p) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new Formula.BoundVariable(FormulaIdentifier.Create(n), ty)], p);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Sp, Cdot, Sp, b, Close);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));

    private static Formula Context(Formula body)
    {
        Formula a = F.Id("A"), l = F.Id("L"), g = F.Id("G");
        Formula data = Call("Data", l, g);
        Formula result = Seq(data, Sp, To, Sp, body);
        return All("A", F.Id("Type"), Seq(
            OpenBracket, Call("NormedRing", a), CloseBracket, Sp,
            OpenBracket, Call("NormedAlgebra", Real, a), CloseBracket, Sp,
            OpenBracket, Call("CompleteSpace", a), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", Real, a), CloseBracket, Sp,
            All("L", Call("LieSubalgebra", Real, a),
                All("G", Call("Subgroup", Call("Units", a)), result))));
    }

    private static Formula TheoremFormula()
    {
        Formula l = F.Id("L");
        Formula x = F.Id("X"), y = F.Id("Y"), c = F.Id("C"), t = F.Id("t");
        Formula hypotheses = And(Rel(x, FormulaRelationOperator.NotEqual, D(0)), Eqn(Call("bracket", x, y), D(0)));
        Formula conclusion = All("X", l, All("Y", l, Imp(hypotheses,
            Ex("c", Real, Eqn(y, Mul(F.Id("c"), x))))));
        return Disp(Context(conclusion));
    }
}
