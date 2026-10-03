using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class RectangleRowmotionHomomesyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy.";
    private static readonly LibraryNoteRef Original =
        LibraryNoteRef.Create("D5/L/Combinatorics/elder2024toggling");
    private static readonly LibraryNoteRef Followup =
        LibraryNoteRef.Create("D5/L/Combinatorics/lafreniere2025intervalclosed");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The max-minus-min statistic is zero-sum on every literal interval-closed rectangle rowmotion orbit.",
        H("Rectangle rowmotion max-minus-min homomesy"),
        Blocks(
            Paragraph(Text(
                "For a finite rectangle Point(m,n) = Fin m × Fin n with coordinatewise order, "
                    + "a complete reverse extension enumerates the points from larger to smaller. "
                    + "During the first N trace steps, each point is visited once and is toggled when "
                    + "symmetric difference preserves interval-closedness. For a fixed input I, "
                    + "trace(e,I,k) equals trace(e,I,N) for every trace index k at least N. "
                    + "One rowmotion step is the unary map rowmotion(e): S ↦ trace(e,S,N); "
                    + "repeated rowmotion applies this whole N-step map to each new input state. "
                    + "The orbit is the finite set of distinct states reached by those applications.")),
            Definition("literalOrbit", "The finite literal rowmotion orbit", LiteralOrbitFormula(),
                "The orbit contains each distinct set state S for which some natural iterate of the actual trace from I equals S. It is a Finset of sets, so every reachable state is counted once; no period, transition identity, or selected finite testing range is assumed."),
            Definition("maxMinusMin", "The integer max-minus-min statistic", MaxMinusMinFormula(),
                "The statistic is the integer cast of the number of globally maximal members of a state minus the integer cast of the number of globally minimal members. It is defined for every set, including the empty set."),
            Describe.Lean(
                DescribeId.Create("rectangle-rowmotion-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The original all-rectangle homomesy conjecture"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Original, Followup),
                Blocks(
                    Paragraph(Text(
                        "For all positive rectangle dimensions, every complete legal reverse extension, "
                            + "and every order-convex initial set, the sum of maxMinusMin over the actual "
                            + "distinct forward orbit states is zero. The proof counts strict rectangular "
                            + "corners with the frozen RectangularCorner theorem, transports endpoint pairs "
                            + "through the literal trace with the frozen RowmotionEndpointTransport theorem, "
                            + "and obtains an integer coboundary. Reversing coordinates supplies the dual "
                            + "count; a recovered reverse trace proves that the literal trace permutes its "
                            + "finite orbit. No global transition law, potential, orbit pairing, width bound, "
                            + "or finite-instance premise is added.")),
                    Paragraph(Text(
                        "This is the exact max-minus-min conjecture stated as Conjecture 4.9 of the "
                            + "published interval-closed-set rowmotion paper and restated as Conjecture 4.2 "
                            + "in the follow-up paper. The repository result settles that original target "
                            + "for every product of two finite chains; the follow-up's separate signed-cardinality "
                            + "result and its other scopes are outside this claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("rectangle-rowmotion-max-minus-min-homomesy"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create("rectangle-rowmotion-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Original),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Point(Formula m, Formula n) => Call("Point", m, n);
    private static Formula SetOf(Formula point) => Call("Set", point);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Paren(left), FormulaLogicOperator.And, Paren(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Paren(left), FormulaLogicOperator.Implies, right);
    private static Formula Count(string variable, Formula domain, Formula predicate) =>
        Call("card", Seq(OpenBrace, F.Id(variable), Sp, InMacro, Sp, domain, Sp, Mid, Sp,
            predicate, CloseBrace));
    private static Formula IntCast(Formula value) => Paren(Seq(value, Colon, Int()));
    private static Formula Iterate(Formula e, Formula k, Formula initial) =>
        Call("iterate", Call("rowmotion", e), k, initial);
    private static Formula Reachable(Formula e, Formula initial, Formula state) =>
        Some("k", Nat(), Equal(Iterate(e, F.Id("k"), initial), state));

    private static Formula LiteralOrbitFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), N = F.Id("N"), e = F.Id("e"), I = F.Id("I");
        Formula point = Point(m, n);
        Formula state = F.Id("S");
        Formula orbit = Seq(F.Id("Finset"), Sp, OpenBrace, state, Sp, InMacro, Sp,
            SetOf(point), Sp, Mid, Sp, Reachable(e, I, state), CloseBrace);
        Formula body = All("m", Nat(), All("n", Nat(), All("N", Nat(),
            All("e", Call("Equiv", Fin(N), point),
                All("I", SetOf(point), Equal(Call("literalOrbit", e, I), orbit))))));
        return Disp(body);
    }

    private static Formula MaxMinusMinFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), I = F.Id("I"), point = Point(m, n);
        Formula maxima = IntCast(Count("a", point, Call("Maximal", I, F.Id("a"))));
        Formula minima = IntCast(Count("u", point, Call("Minimal", I, F.Id("u"))));
        Formula body = All("m", Nat(), All("n", Nat(),
            All("I", SetOf(point), Equal(Call("maxMinusMin", I),
                new Formula.Binary(maxima, FormulaBinaryOperator.Subtract, minima)))));
        return Disp(body);
    }

    private static Formula ResultFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n"), N = F.Id("N"), e = F.Id("e"), I = F.Id("I");
        Formula point = Point(m, n);
        Formula orbit = Call("literalOrbit", e, I);
        Formula sum = Seq(Sum, Underscore, Grp(Seq(F.Id("S"), Sp, InMacro, Sp, orbit)), Sp,
            Call("maxMinusMin", F.Id("S")));
        Formula legal = All("e", Call("Equiv", Fin(N), point),
            Imp(Call("ReverseExtension", e),
                All("I", SetOf(point), Imp(Call("OrdConnected", I), Equal(sum, D(0))))));
        Formula body = All("m", Nat(), All("n", Nat(), All("N", Nat(),
            Imp(And(Rel(D(0), FormulaRelationOperator.LessThan, m),
                     Rel(D(0), FormulaRelationOperator.LessThan, n)), legal))));
        return Disp(body);
    }
}
