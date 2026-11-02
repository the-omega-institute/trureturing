using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CyclicBoolean.CyclicSignTrace;

internal sealed class CyclicSignTraceTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace/Trace.";
    private static readonly LibraryNoteRef SourceNote =
        LibraryNoteRef.Create("D5/L/Fourier/ricardorr2026mo512655");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordered integer matrix trace is exactly the Boolean phase sum for every positive length.",
        H("The exact ordered trace bridge"),
        Blocks(
            Describe.Lean(DescribeId.Create("cyclic-sign-trace-source-trace-eq-phase-sum"),
                DeclarationHandle.Create(Prefix + "sourceTrace_eq_phase_sum"),
                H("The ordered trace is the exact Boolean phase sum"),
                StatementSource.FromAuthor(CyclicSignTraceScribeFormulas.TracePhaseFormula()),
                AssessedProvenance.FromRepo(SourceNote),
                Blocks(
                    Paragraph(Text("At every positive length n and for all words b,a, the literal ordered matrix trace is the sum over every x of sign(dot(b,x)+dot(a,chi(x))). Length one and all coincident cyclic indices are included. This identity also applies to even lengths; oddness is needed only for the inverse construction.")),
                    Paragraph(Text("For a list of r+1 matrices, expand its (i,j) entry over all r intermediate states. The row tuple is i followed by the intermediate states; the column tuple is those states followed by j. Induction uses the first matrix factor and the ordinary Matrix.mul entry formula, preserving the complete list order. Taking the trace identifies j with i. Joining the initial state to the intermediate tuple gives every cyclic path exactly once; the final column is the initial state, including for a one-factor product.")),
                    Paragraph(Text("The path product is the sign of the sum of its entry exponents. Reindex the a_(k-2)x_k term by k=i+2 and the a_(k-1)x_k x_(k+1) term by k=i+1. The coefficient of a_i becomes x_i+x_(i+2)+x_(i+1)x_(i+2), exactly chi(x)_i. These are bijections of the actual cyclic index set, so repeated indices need no separate independence assumption."))
                ), DescribeRole.Theorem)
        ), []));
}

internal static class CyclicSignTraceScribeFormulas
{
    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula All(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, body);
    private static Formula Some(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.And, Grp(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.Implies, Grp(b));
    private static Formula Bin(Formula a, FormulaBinaryOperator op, Formula b) => new Formula.Binary(Grp(a), op, Grp(b));
    private static Formula Plus(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Add, b);
    private static Formula Times(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Word(Formula n) => Call("Word", n);
    private static Formula Sum(string x, Formula t, Formula body) => Seq(F.Sum, Underscore, Grp(F.Id(x), Sp, InMacro, Sp, t), Sp, body);
    private static Formula OddLength(Formula m) => Plus(Times(D(2), m), D(1));

    internal static Formula InverseFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x"), y = F.Id("y"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"),
            And(All("x", w, Eq(Call("inverse", m, Call("chi", x)), x)),
                All("y", w, Eq(Call("chi", Call("inverse", m, y)), y)))));
    }

    internal static Formula InversionFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), y = F.Id("y"), a = F.Id("a"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, Call("ZMod", D(2))), All("y", w,
                Eq(Sum("a", w, Times(Call("walsh", f, a), Call("sign", Call("dot", a, y)))),
                    Times(Call("card", w), Call("sign", Call("f", y)))))))));
    }

    internal static Formula NonemptyFormula()
    {
        Formula n = F.Id("n"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, Call("ZMod", D(2))), Some("a", w,
                Rel(Call("walsh", F.Id("f"), F.Id("a")), FormulaRelationOperator.NotEqual, D(0)))))));
    }

    internal static Formula PhaseNonemptyFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"), All("b", w, Some("a", w,
            Rel(Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x))))),
                FormulaRelationOperator.NotEqual, D(0))))));
    }

    internal static Formula PhaseFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"), All("b", w, All("a", w,
            Eq(Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x))))),
                Call("walsh", Call("inverseComponent", m, b), a))))));
    }

    internal static Formula WalshDerivativeFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), u = F.Id("u"), c = F.Id("c"),
            y = F.Id("y"), a = F.Id("a"), w = Word(n), bit = Call("ZMod", D(2));
        Formula derivative = All("y", w,
            Eq(Plus(Call("f", Plus(y, u)), Call("f", y)), c));
        Formula support = All("a", w,
            Imp(new Formula.Relation(Call("walsh", f, a), FormulaRelationOperator.NotEqual, D(0)),
                Eq(Call("dot", a, u), c)));
        return Disp(All("n", Named("Nat"),
            Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
                All("f", Arrow(w, bit), All("u", w, All("c", bit,
                    new Formula.Logic(Grp(derivative), FormulaLogicOperator.Iff,
                        Grp(support))))))));
    }

    internal static Formula AffineDualityFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), u = F.Id("u"), c = F.Id("c"), y = F.Id("y"),
            w = Word(n), bit = Call("ZMod", D(2));
        Formula derivative = Some("c", bit,
            All("y", w, Eq(Plus(Call("f", Plus(y, u)), Call("f", y)), c)));
        Formula membership = Call("mem", u, Call("constantDerivativeSubmodule", f));
        Formula finrankD = Call("finrank", bit, Call("constantDerivativeSubmodule", f));
        Formula finrankA = Call("finrank", bit, Call("walshSupportDirection", f));
        Formula finrankV = Call("finrank", bit, w);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, bit),
                And(All("u", w,
                        new Formula.Logic(Grp(membership), FormulaLogicOperator.Iff,
                            Grp(derivative))),
                    Eq(Plus(finrankD, finrankA), finrankV))))));
    }

    internal static Formula TracePhaseFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("b", w, All("a", w,
                Eq(Call("sourceTrace", b, a),
                    Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x)))))))))));
    }

    internal static Formula BooleanCoefficientFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), s = F.Id("s"), i = F.Id("i"), r = F.Id("r"),
            n = OddLength(m), p = Call("prefixVariables", i, r);
        Formula delta(Formula t) => Call("ite", Eq(s, t), D(1), D(0));
        Formula endpoint = Plus(i, Times(D(2), r));
        Formula rhs = Sum("i", Call("ZMod", n), Sum("r", Call("range", Plus(m, D(1))),
            Times(Call("b", i), Plus(delta(p), delta(Call("insert", endpoint, p))))));
        Formula shifted = Seq(Grp(F.Id("z"), F.Colon, Word(n)), F.Mapsto,
            Call("inverseComponent", m, b, Plus(D(1), F.Id("z"))));
        return Disp(All("m", Named("Nat"), All("b", Word(n),
            All("s", Call("Finset", Call("ZMod", n)), Eq(Call("booleanCoeff", shifted, s), rhs)))));
    }

    internal static Formula DerivativeCoefficientFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), u = F.Id("u"), s = F.Id("s"),
            i = F.Id("i"), r = F.Id("r"), y = F.Id("y"), n = OddLength(m), p = Call("prefixVariables", i, r);
        Formula constant = Some("c", Call("ZMod", D(2)), All("y", Word(n),
            Eq(Plus(Call("inverseComponent", m, b, Plus(y, u)), Call("inverseComponent", m, b, y)), F.Id("c"))));
        Formula rhs = Sum("i", Call("ZMod", n), Sum("r", Call("range", Plus(m, D(1))),
            Times(Call("b", i), Plus(Call("monomialDerivativeCoeff", p, s, u),
                Call("monomialDerivativeCoeff", Call("insert", Plus(i, Times(D(2), r)), p), s, u)))));
        return Disp(All("m", Named("Nat"), All("b", Word(n), All("u", Word(n),
            Imp(constant, All("s", Call("Finset", Call("ZMod", n)),
                Imp(Call("Nonempty", s), Eq(rhs, D(0)))))))));
    }

    internal static Formula TopCoefficientFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), i = F.Id("i"), n = OddLength(m);
        Formula shifted = Seq(Grp(F.Id("z"), F.Colon, Word(n)), F.Mapsto,
            Call("inverseComponent", m, b, Plus(D(1), F.Id("z"))));
        return Disp(All("m", Named("Nat"), All("b", Word(n), All("i", Call("ZMod", n),
            Eq(Call("booleanCoeff", shifted, Call("topVariables", m, i)), Call("b", i))))));
    }

    internal static Formula TopDerivativeFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), u = F.Id("u"), s = F.Id("s"),
            i = F.Id("i"), n = OddLength(m), t = Call("topVariables", m, i);
        Formula summand = Times(Call("b", i), Call("ite", Call("subset", s, t),
            Call("booleanMonomial", Call("sdiff", t, s), u), D(0)));
        Formula sets = All("s", Call("Finset", Call("ZMod", n)),
            Imp(Eq(Call("card", s), m), Eq(Sum("i", Call("ZMod", n), summand), D(0))));
        Formula directions = All("b", Word(n), All("u", Word(n), Imp(
            Call("mem", u, Call("constantDerivativeSubmodule", Call("inverseComponent", m, b))), sets)));
        return Disp(All("m", Named("Nat"),
            Imp(Rel(D(0), FormulaRelationOperator.LessThan, m), directions)));
    }

    internal static Formula SupportDimensionFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), n = OddLength(m), bit = Call("ZMod", D(2));
        Formula rank = Call("finrank", bit, Call("direction", Call("affineSpan", bit, Call("traceSupport", b))));
        return Disp(All("m", Named("Nat"), All("b", Word(n), Imp(
            Rel(b, FormulaRelationOperator.NotEqual, D(0)),
            Rel(Times(D(2), m), FormulaRelationOperator.LessThanOrEqual, rank)))));
    }
}
