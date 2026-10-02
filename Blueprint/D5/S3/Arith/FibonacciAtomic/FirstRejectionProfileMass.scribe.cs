using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FirstRejectionProfileMassDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/FirstRejectionProfileMass.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Left, Open, f, Right, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, Par(Seq(variable, Colon, Sp, type)), Comma, Sp, body));
    private static Formula SumOf(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(variable, Sp, InMacro, Sp, type)), Sp, body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual uniform window-cut profile mass equals its chronological two-state "
        + "matrix value, is positive, and the profile masses sum to one.",
        H("Two-State Profile Mass for Every Window Cut"),
        Blocks(
            Paragraph(Text("Fix k≥0 and n=k+1. Positions are indexed by Fin(n), starting at zero. "
                + "A is any finite set of positions and B is its complement. The alphabet Window "
                + "consists of the five complete windows 000,100,010,101,001, written from low to "
                + "high. Owned(k,A) is the subtype of Fin(n) consisting of positions in A, and "
                + "Side(k,A) is the function type Owned(k,A) to Window. The law "
                + "profileLaw(k,A) has type FiniteResponseLaw(Side(k,A)): its rational mass is "
                + "nonnegative and its total is one. It is the independent product of the actual "
                + "five-window laws with mass 1/5, so each assignment has mass 5 to the power "
                + "minus card(A). There is no legality "
                + "restriction on the raw assignments.")),
            Paragraph(Text("Profile(k,A) consists of an allowed cutoff and its active crossing bits. "
                + "profileMass(P) is the pushforward mass of code(A) at encode(P), namely the "
                + "sum of profileLaw(k,A).mass(a) over that actual fiber. Equivalently it is the "
                + "uniform finite mean of the fiber indicator. The code and encode maps identify "
                + "that fiber. The cutoff records "
                + "the earliest bad A-internal seam, the terminal zero window when the terminal "
                + "position belongs to A, or top when neither occurs. A seam j has left position j "
                + "and right position j+1. A retained crossing has j strictly before the cutoff. "
                + "Its owned high or low bit is required to equal the encoded bit. When the cutoff "
                + "is terminal, only the crossing into the terminal position has its low bit forced "
                + "to false by encode; earlier independent crossing ports retain their own bits.")),
            Paragraph(Text("filterWindow(P,i,x) checks all retained crossing ports owned by i. "
                + "At the terminal position it additionally requires x=000 for the terminal "
                + "cutoff, x≠000 for top, and nothing for an earlier internal cutoff. "
                + "internalFactor(P,j,r,u) is one minus the product of the two Bool bits when j "
                + "is A-internal and before the cutoff, their product when j equals the cutoff, "
                + "and one otherwise. seamFactor uses this factor at the seam immediately before "
                + "the current position, and is one at position zero. Thus the rejecting seam "
                + "keeps both its endpoints constrained, while every later raw window is free.")),
            Paragraph(Text("The public matrix D at an A position has entry (r,v) equal to one "
                + "fifth of the sum over all five actual windows x of the indicator high(x)=v, "
                + "the window filter, and seamFactor(P,i,r,low(x)). This average preserves the "
                + "difference between 000 and 010. At a B position its entry is the indicator "
                + "v=false, for both input states, with weight one. Matrices are multiplied in "
                + "chronological position order. Each matrix is rational and indexed by Bool in "
                + "both directions. matrixProduct(P) denotes this ordered product; "
                + "summing its false initial row over both final Bool states gives the scalar "
                + "profileOperatorMass(P).")),
            Paragraph(Text("For every prefix length m≤n, restrict a uniform raw m-window tuple "
                + "to the coordinates owned by A. This restriction has exactly their actual "
                + "product law. Complementary coordinates integrate to one. The accepted-prefix "
                + "mass with saved state v equals the false,v entry of the first m matrix factors. "
                + "The saved state is the immediately preceding window's high bit after A and "
                + "false after B. Final-coordinate integration gives the five-window A average "
                + "and the weight-one B reset. At m=n, acceptance of all filters is equivalent to "
                + "code(A,a)=encode(P). Every profile has a representative of positive weight, "
                + "and the profile fibers partition Side(k,A). In particular the empty cut has "
                + "one assignment and scalar mass one.")),
            Describe.Lean(DescribeId.Create("first-rejection-profile-mass"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Actual profile fibers and exact two-state probabilities"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All statements hold for every natural k, arbitrary A, "
                    + "reachable profile P, and actual A assignment a. In the formula, index(i) "
                    + "is the underlying position of the owned-coordinate subtype. extend(A,a) "
                    + "fills B with the middle window, whose two endpoint bits are false. "
                    + "The first clause gives the exact atom mass. The second identifies the "
                    + "whole fiber with its window and internal-seam filters. The third gives "
                    + "the chronological matrix value and its strict positivity. The last sums "
                    + "the actual profile probabilities to one."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var k = V("k");
        var A = V("A");
        var P = V("P");
        var a = V("a");
        var i = V("i");
        var j = V("j");
        var v = V("v");
        var n = Seq(k, Plus, D(1));
        var profiles = Call("Profile", k, A);
        var side = Call("Side", k, A);
        var atomMass = All(a, side,
            EqOf(Call("mass", Call("profileLaw", k, A), a),
                new Formula.Fraction(D(1), new Formula.Power(D(5), Call("card", A)))));
        var windowFilters = All(i, Call("Owned", k, A),
            EqOf(Call("filterWindow", P, Call("index", i), Call("apply", a, i)), V("true")));
        var word = Call("extend", A, a);
        var seamFilters = All(j, Call("Fin", k),
            EqOf(Call("internalFactor", P, j,
                Call("last", Call("apply", word, Call("left", j))),
                Call("first", Call("apply", word, Call("right", j)))), D(1)));
        var eventClause = All(P, profiles, All(a, side,
            Par(Seq(EqOf(Call("code", A, a), Call("encode", P)), Sp, Iff, Sp,
                And(windowFilters, seamFilters)))));
        var mass = Call("profileMass", P);
        var matrixValue = SumOf(v, Call("Bool"),
            Call("entry", Call("matrixProduct", P), V("false"), v));
        var massClause = All(P, profiles,
            And(EqOf(mass, matrixValue), Seq(D(0), Sp, Lt, Sp, mass)));
        var normalized = EqOf(SumOf(P, profiles, Call("profileMass", P)), D(1));
        return Disp(All(k, Call("Nat"), All(A, Call("Finset", Call("Fin", n)),
            And(atomMass, And(eventClause, And(massClause, normalized))))));
    }
}
